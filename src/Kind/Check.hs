module Kind.Check where

import Kind.Type
import Kind.Env
import Kind.Reduce
import Kind.Equal
import Kind.Show

import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M

import Control.Monad (forM_)
import Debug.Trace

-- Type-Checking
-- -------------

-- Note that, for type-checking, instead of passing down contexts (as usual), we
-- just annotate variables (with a `{x: T}` type hint) and check. This has the
-- same effect, while being slightly more efficient. Type derivations comments
-- are written in this style too.

-- ### Inference

infer :: Term -> Int -> Env Term
infer term dep = {-trace ("infer: " ++ termShower True term dep) $-} go term dep where
  -- inp : Set
  -- (bod {nam: inp}) : Set
  -- ----------------------- function
  -- (∀(nam: inp) bod) : Set
  go (All nam inp bod) dep = do
    envSusp (Check Nothing inp Set dep)
    envSusp (Check Nothing (bod (Ann False (Var nam dep) inp)) Set (dep + 1))
    return Set

  -- fun : ∀(ftyp_nam: ftyp_inp) ftyp_bod
  -- arg : ftyp_inp
  -- ------------------------------------ application
  -- (fun arg) : (ftyp_bod arg)
  go (App fun arg) dep = do
    ftyp <- infer fun dep
    book <- envGetBook
    fill <- envGetFill
    case reduce book fill 2 ftyp of
      (All ftyp_nam ftyp_inp ftyp_bod) -> do
        envSusp (Check Nothing arg ftyp_inp dep)
        return $ ftyp_bod arg
      otherwise -> do
        envLog (Error Nothing (Hol "function" []) ftyp (App fun arg) dep)
        envFail

  --
  -- ---------------- annotation (infer)
  -- {val: typ} : typ
  go (Ann chk val typ) dep = do
    if chk then do
      check Nothing val typ dep
    else do
      return ()
    return typ

  -- (bod {nam: typ}) : Set
  -- ----------------------- self-type
  -- ($(nam: typ) bod) : Set
  go (Slf nam typ bod) dep = do
    envSusp (Check Nothing (bod (Ann False (Var nam dep) typ)) Set (dep + 1))
    return Set

  -- val : $(vtyp_nam: vtyp_typ) vtyp_bod
  -- ------------------------------------ self-inst (infer)
  -- ~val : (vtyp_bod (~val))
  go (Ins val) dep = do
    vtyp <- infer val dep
    book <- envGetBook
    fill <- envGetFill
    case reduce book fill 2 vtyp of
      (Slf vtyp_nam vtyp_typ vtyp_bod) -> do
        return $ vtyp_bod (Ins val)
      otherwise -> do
        envLog (Error Nothing (Hol "self-type" []) vtyp (Ins val) dep)
        envFail

  -- T0: * ...
  -- --------------------------------- data
  -- %Foo{ #C0 { x0:T0 ... } ... } : *
  go (Dat scp cts) dep = do
    forM_ cts $ \ (Ctr _ fs rt) -> do
      forM_ fs $ \ (_, ty) -> do
        envSusp (Check Nothing ty Set dep)
      envSusp (Check Nothing rt Set dep)
    return Set

  -- val : T
  -- ----------------- reference
  -- (Ref nam) : T
  go (Ref nam) dep = do
    book <- envGetBook
    case M.lookup nam book of
      Just val -> infer val dep
      Nothing  -> do
        envLog (Error Nothing (Hol "undefined_reference" []) (Hol "unknown_type" []) (Ref nam) dep)
        envFail

  -- ...
  -- --------- type-in-type
  -- Set : Set
  go Set dep = do
    return Set

  -- ...
  -- --------- U32-type
  -- U32 : Set
  go U32 dep = do
    return Set

  -- ...
  -- ----------- U32-value
  -- <num> : U32
  go (Num num) dep = do
    return U32

  -- ...
  -- -------------- String-literal
  -- "txt" : String
  go (Txt txt) dep = do
    return (Ref "String")

  -- ...
  -- --------- Nat-literal
  -- 123 : Nat
  go (Nat val) dep = do
    return (Ref "Nat")

  -- fst : U32
  -- snd : U32
  -- ----------------- U32-operator
  -- (+ fst snd) : U32
  go (Op2 opr fst snd) dep = do
    envSusp (Check Nothing fst U32 dep)
    envSusp (Check Nothing snd U32 dep)
    return U32

  -- x : U32
  -- p : U32 -> Set
  -- z : (p 0)
  -- s : (n: U32) -> (p (+ 1 n))
  -- ------------------------------------- U32-elim
  -- (switch x { 0: z ; _: s }: p) : (p x)
  go (Swi nam x z s p) dep = do
    envSusp (Check Nothing x U32 dep)
    envSusp (Check Nothing (p (Ann False (Var nam dep) U32)) Set dep)
    envSusp (Check Nothing z (p (Num 0)) dep)
    envSusp (Check Nothing (s (Ann False (Var (nam ++ "-1") dep) U32)) (p (Op2 ADD (Num 1) (Var (nam ++ "-1") dep))) (dep + 1))
    return (p x)

  -- val : typ
  -- (bod {nam: typ}) : T
  -- ------------------------ let-binder (infer)
  -- (let nam = val; bod) : T
  go (Let nam val bod) dep = do
    typ <- infer val dep
    infer (bod (Ann False (Var nam dep) typ)) dep

  -- (bod val) : T
  -- ------------------------ use-binder (infer)
  -- (use nam = val; bod) : T
  go (Use nam val bod) dep = do
    infer (bod val) dep

  -- Can't infer #
  go (Con nam arg) dep = do
    envLog (Error Nothing  (Hol "type_annotation" []) (Hol "untyped_constructor" []) (Con nam arg) dep)
    envFail

  -- Can't infer λ{}
  go (Mat cse) dep = do
    envLog (Error Nothing  (Hol "type_annotation" []) (Hol "untyped_match" []) (Mat cse) dep)
    envFail

  -- Can't Infer λ
  go (Lam nam bod) dep = do
    envLog (Error Nothing  (Hol "type_annotation" []) (Hol "untyped_lambda" []) (Lam nam bod) dep)
    envFail

  -- Can't Infer ?
  go (Hol nam ctx) dep = do
    envLog (Error Nothing  (Hol "type_annotation" []) (Hol "untyped_hole" []) (Hol nam ctx) dep)
    envFail

  -- Can't Infer _
  go (Met uid spn) dep = do
    envLog (Error Nothing  (Hol "type_annotation" []) (Hol "untyped_meta" []) (Met uid spn) dep)
    envFail

  -- Can't Infer x
  go (Var nam idx) dep = do
    envLog (Error Nothing  (Hol "type_annotation" []) (Hol "untyped_variable" []) (Var nam idx) dep)
    envFail

  -- Src-passthrough
  go (Src src val) dep = do
    infer val dep

check :: Maybe Cod -> Term -> Term -> Int -> Env ()
check src val typ dep = {-trace ("check: " ++ termShower True val dep ++ "\n    :: " ++ termShower True typ dep) $-} go src val typ dep where
  -- (bod {typ_nam: typ_inp}) : (typ_bod {nam: typ_inp})
  -- --------------------------------------------------- lambda
  -- (λnam bod) : (∀(typ_nam: typ_inp) typ_bod)
  go src (Lam nam bod) typx dep = do
    book <- envGetBook
    fill <- envGetFill
    case reduce book fill 2 typx of
      (All typ_nam typ_inp typ_bod) -> do
        let ann = Ann False (Var nam dep) typ_inp
        check Nothing (bod ann) (typ_bod ann) (dep + 1)
      otherwise -> do
        infer (Lam nam bod) dep
        return ()

  -- val : (typ_bod ~val)
  -- ---------------------------------- self-inst (check)
  -- ~val : $(typ_nam: typ_typ) typ_bod
  go src (Ins val) typx dep = do
    book <- envGetBook
    fill <- envGetFill
    case reduce book fill 2 typx of
      Slf typ_nam typ_typ typ_bod -> do
        check Nothing val (typ_bod (Ins val)) dep
      _ -> do
        infer (Ins val) dep
        return ()

  -- TODO: comment constructor checker
  go src val@(Con nam arg) typx dep = do
    book <- envGetBook
    fill <- envGetFill
    case reduce book fill 2 typx of
      (Dat adt_scp adt_cts) -> do
        case lookup nam (map (\(Ctr cnm cfs crt) -> (cnm, (cfs, crt))) adt_cts) of
          Just (cfs,crt) -> do
            if length cfs == length arg then do
              forM_ (zip arg cfs) $ \(a, (_, t)) -> do
                check Nothing a t dep
              cmp src val crt typx dep
            else do
              envLog (Error Nothing (Hol "constructor_arity_mismatch" []) (Hol "unknown_type" []) (Con nam arg) dep)
              envFail
          Nothing -> do
            envLog (Error Nothing (Hol ("constructor_not_found:"++nam) []) (Hol "unknown_type" []) (Con nam arg) dep)
            envFail
      _ -> {-trace ("OXI " ++ termShower True (reduce book fill 2 typx) dep) $-} do
        infer (Con nam arg) dep
        return ()

  -- TODO: comment match checker
  -- go src (Mat cse) typx dep = do
    -- book <- envGetBook
    -- fill <- envGetFill
    -- case reduce book fill 2 typx of
      -- (All typ_nam typ_inp typ_bod) -> do
        -- case reduce book fill 2 typ_inp of
          -- (Dat adt_scp adt_cts) -> do
            -- let adt_cts_map = M.fromList (map (\ (Ctr cnm cfs crt) -> (cnm, (cfs, crt))) adt_cts)
            -- forM_ cse $ \ (cnm, cbod) -> do
              -- case M.lookup cnm adt_cts_map of
                -- Just (cfs,crt) -> do
                  -- -- TODO: for debugging purposes, print ALL definitions inside book, and their terms
                  -- forM_ (M.toList book) $ \(k, v) -> do
                    -- trace ("Definition: " ++ k ++ " = " ++ termShower True v dep) $ return ()
                  -- let ann = Ann False (Con cnm (map (\ (fn, ft) -> Var fn dep) cfs)) typ_inp
                  -- let bty = foldr (\(fn, ft) acc -> All fn ft (\x -> acc)) (typ_bod ann) cfs
                  -- let ext = \ (Dat as _) (Dat bs _) -> zipWith (\ (Var _ i) v -> (i,v)) as bs
                  -- let sub = ext (reduce book fill 2 typ_inp) (reduce book fill 2 crt)
                  -- let rty = foldl' (\ ty (i,t) -> subst i t ty) bty sub
                  -- check Nothing cbod rty dep
                -- Nothing -> do
                  -- envLog (Error Nothing (Hol ("constructor_not_found:"++cnm) []) (Hol "unknown_type" []) (Mat cse) dep)
                  -- envFail
          -- _ -> do
            -- infer (Mat cse) dep
            -- return ()
      -- _ -> do
        -- infer (Mat cse) dep
        -- return ()
  -- TODO: refactor the Mat case above so that 'ext' is a separate function.
  -- add a default case for when it isn't the case that both terms are Dat. in that case, debug-trace both terms, and return an error.
  -- also move the function inside zipWith out, add a default case to it. debug-trace when the first isn't var, and default to (0,v).
  -- remember: move these functions to a SEPARATE place using a 'where' block
  
  go src (Mat cse) typx dep = do
    book <- envGetBook
    fill <- envGetFill
    case reduce book fill 2 typx of
      (All typ_nam typ_inp typ_bod) -> do
        case reduce book fill 2 typ_inp of
          (Dat adt_scp adt_cts) -> do
            let adt_cts_map = M.fromList (map (\ (Ctr cnm cfs crt) -> (cnm, (cfs, crt))) adt_cts)
            forM_ cse $ \ (cnm, cbod) -> do
              case M.lookup cnm adt_cts_map of
                Just (cfs,crt) -> do
                  let ann = Ann False (Con cnm (map (\ (fn, ft) -> Var fn dep) cfs)) typ_inp
                  let bty = foldr (\(fn, ft) acc -> All fn ft (\x -> acc)) (typ_bod ann) cfs
                  let sub = ext (reduce book fill 2 typ_inp) (reduce book fill 2 crt)
                  let rty = foldl' (\ ty (i,t) -> subst i t ty) bty sub
                  check Nothing cbod rty dep
                Nothing -> do
                  envLog (Error Nothing (Hol ("constructor_not_found:"++cnm) []) (Hol "unknown_type" []) (Mat cse) dep)
                  envFail
          _ -> do
            infer (Mat cse) dep
            return ()
      _ -> do
        infer (Mat cse) dep
        return ()
    where
      ext :: Term -> Term -> [(Int, Term)]
      ext (Dat as _) (Dat bs _) = zipWith extHelper as bs
      ext a          b          = trace ("Unexpected terms in ext: " ++ termShower True a dep ++ " and " ++ termShower True b dep) []

      extHelper :: Term -> Term -> (Int, Term)
      extHelper (Var _ i) v = (i, v)
      extHelper (Src _ i) v = extHelper i v
      extHelper a         v = trace ("Unexpected first term in extHelper: " ++ termShower True a dep) (0, v)



  -- val : typ
  -- (bod {nam: typ}) : T
  -- ------------------------ let-binder (check)
  -- (let nam = val; bod) : T
  go src (Let nam val bod) typx dep = do
    typ <- infer val dep
    check Nothing (bod (Ann False (Var nam dep) typ)) typx dep

  -- (bod val) : T
  -- ------------------------ use-binder (check)
  -- (use nam = val; bod) : T
  go src (Use nam val bod) typx dep = do
    check Nothing (bod val) typx dep

  -- ...
  -- ------ inspection
  -- ?A : T
  go src (Hol nam ctx) typx dep = do
    envLog (Found nam typx ctx dep)
    return ()

  -- ...
  -- ----- metavar
  -- _ : T
  go src (Met uid spn) typx dep = do
    return ()

  -- ...
  -- ---------------- annotation (check)
  -- {val: typ} : typ
  go src (Ann chk val typ) typx dep = do
    cmp src val typ typx dep
    if chk then do
      check src val typ dep
    else do
      return ()

  -- val : T
  -- ------- source (just skipped)
  -- val : T
  go _ (Src src val) typx dep = do
    check (Just src) val typx dep

  -- A == B
  -- val : A
  -- -------
  -- val : B
  go src term typx dep = do
    infer <- infer term dep
    cmp src term typx infer dep

  -- Checks types equality and reports
  cmp src term expected detected dep = {-trace ("cmp " ++ termShower True expected dep ++ " " ++ termShower True detected dep) $-} do
    equal <- equal expected detected dep
    if equal then do
      susp <- envTakeSusp
      forM_ susp $ \ (Check src val typ dep) -> do
        go src val typ dep
      return ()
    else do
      envLog (Error src expected detected term dep)
      envFail

doCheck :: Term -> Env ()
doCheck (Ann _ val typ) = check Nothing val typ 0 >> return ()
doCheck (Src _ val)     = doCheck val
doCheck (Ref nam)       = doCheckRef nam
doCheck term            = infer term 0 >> return ()

doCheckRef :: String -> Env ()
doCheckRef nam = do
  book <- envGetBook
  case M.lookup nam book of
    Just val -> doCheck val
    Nothing  -> envLog (Error Nothing (Hol "undefined_reference" []) (Hol "unknown_type" []) (Ref nam) 0) >> envFail
