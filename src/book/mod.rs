use crate::{*};

use std::collections::BTreeMap;
use std::collections::BTreeSet;

mod compile;
mod parse;
mod show;

// <book> ::=
//   USE | use <alias> <book>
//   ADT | <adt> <book>
//   ANN | <name> : <term> = <term> <book>
//   DEF | <name> = <term> <book>
//   END | <eof>
#[derive(Clone, Debug)]
pub struct Book {
  pub defs: BTreeMap<String, Term>,
  pub fids: BTreeMap<String, u64>,
}

// Shadows a name on the uses map
pub fn shadow(key: &str, uses: &Uses) -> Uses {
  let mut uses = uses.clone();
  uses.insert(key.to_string(), key.to_string());
  return uses;
}

// Maps short names ("cons") to full names ("List/cons")
pub type Uses = im::HashMap<String, String>;

impl Book {

  // Creates an empty book
  pub fn new() -> Self {
    Book {
      defs: BTreeMap::new(),
      fids: BTreeMap::new(),
    }
  }

  // Creates a book, loading a term, its dependencies, and stdlib
  pub fn boot(base: &str, name: &str) -> Result<Self, String> {
    let mut book = Book::new();
    book.load(base, name)?;
    book.load(base, "String")?;
    book.load(base, "String/cons")?;
    book.load(base, "String/nil")?;
    book.load(base, "Nat")?;
    book.load(base, "Nat/succ")?;
    book.load(base, "Nat/zero")?;
    book.expand_implicits();
    return Ok(book);
  }

  // Handles an unbound definition
  pub fn handle_unbound(&self, file: &str, name: &str) -> Result<(), String> {
    return Err(format!("ERROR\n- unbound: '{}'\n- on_file: {}", name, file));
  }

  // Same as load, mutably adding to a 'book'
  pub fn load(&mut self, base: &str, name: &str) -> Result<(), String> {
    let name = name.trim_end_matches('/'); // last "/" is not part of name
    if !self.defs.contains_key(name) {
      // Parses a file into a new book
      let file = format!("{}/{}.kind2", base, name);
      let (file, text) = match std::fs::read_to_string(&file) {
        Ok(content) => (file, content),
        Err(_) => {
          let backup_file = format!("{}/{}/_.kind2", base, name);
          let text = std::fs::read_to_string(&backup_file).map_err(|_| format!("Could not read file: {} or {}", file, backup_file))?;

          (backup_file, text)
        }
      };
      let fid  = self.get_file_id(&file);
      let defs = KindParser::new(&text).parse_book(name, fid)?;
      // Merges new book into book
      for (def_name, def_value) in &defs.defs {
        self.defs.insert(def_name.clone(), def_value.clone());
      }
      // Finds dependencies and loads them
      for (def_name, def_term) in defs.defs.into_iter() {
        let mut dependencies = BTreeSet::new();
        def_term.get_free_vars(im::Vector::new(), &mut dependencies);
        for ref_name in dependencies {
          if let Err(_) = self.load(&base, &ref_name) {
            // If `ref_name` is an unbound constructor of the ADT `def_term`,
            // we can generate it.
            let maybe_ctr = Term::constructor_code((&def_name, &def_term), &ref_name);

            if let Some(ctr_code) = maybe_ctr {
              let ctr_code = ctr_code.flatten(Some(80));

              let file_name = format!("{}.kind2", ref_name.trim_end_matches('/'));
              let file_path = std::path::Path::new(&file_name);
              let err = || format!("ERROR: could not create file for generated constructor {ref_name}");

              // Create folder structure
              std::fs::create_dir_all(file_path.parent().ok_or_else(err)?).map_err(|_| err())?;
              // Write constructor to its own file.
              // It rewrites the file if it already exists.
              // TODO: If the ADT definition does not type check, the wrong constructor
              //       is still written to its own file. What should I do in this case?
              std::fs::write(&file_name, ctr_code).map_err(|_| err())?;

              self.load(&base, &ref_name)?;
              continue;
            }

            self.handle_unbound(&file, &ref_name)?;
          }
        }
      }
    }
    return Ok(());
  }

  // Desugars all definitions
  pub fn expand_implicits(&mut self) {
    // Creates a map with the implicit count of each top-level definition
    let mut implicit_count = BTreeMap::new();
    for (name, term) in self.defs.iter() {
      implicit_count.insert(name.clone(), term.count_implicits());
    }
    // Expands implicit calls of each top-level definition in the book
    for def in self.defs.iter_mut() {
      def.1.expand_implicits(im::Vector::new(), &implicit_count);
    }
  }

  // Gets a file id from its name
  pub fn get_file_id(&mut self, name: &str) -> u64 {
    if let Some(id) = self.fids.get(name) {
      *id
    } else {
      let id = self.fids.len() as u64 + 1;
      self.fids.insert(name.to_string(), id);
      id
    }
  }

  // Gets a file name from its id (FIXME: asymptotics)
  pub fn get_file_name(&self, id: u64) -> Option<String> {
    for (name, &fid) in &self.fids {
      if fid == id {
        return Some(name.clone());
      }
    }
    None
  }

}

#[cfg(test)]
mod tests {
  use crate::*;

  // TODO: this could be in the `sugar` module
  fn extract_adt(t: &Term) -> &Term {
    match t {
      Term::Lam { bod, .. } => extract_adt(bod),
      Term::Ann { val, .. } => extract_adt(val),
      Term::Src { val, .. } => extract_adt(val),
      // Found ADT
      Term::Slf { .. } => t,
      // Couldn't find ADT
      _ => t,
    }
  }

  // TODO: this could be in the `term` module
  fn apply(t: &Term, f: impl Fn(&Term) -> Term) -> Term {
    match t {
      Term::All { era, nam, inp, bod } => {
        Term::All { era: *era, nam: nam.clone(), inp: Box::new(f(inp)), bod: Box::new(f(bod)) }
      }
      Term::Lam { era, nam, bod } => Term::Lam { era: *era, nam: nam.clone(), bod: Box::new(f(bod)) },
      Term::App { era, fun, arg } => Term::App { era: *era, fun: Box::new(f(fun)), arg: Box::new(f(arg)) },
      Term::Ann { chk, val, typ } => Term::Ann { chk: *chk, val: Box::new(f(val)), typ: Box::new(f(typ)) },
      Term::Slf { nam, typ, bod } => {
        Term::Slf { nam: nam.clone(), typ: Box::new(f(typ)), bod: Box::new(f(bod)) }
      }
      Term::Ins { val } => Term::Ins { val: Box::new(f(val)) },
      Term::Set => Term::Set,
      Term::U60 => Term::U60,
      Term::Num { val } => Term::Num { val: *val },
      Term::Op2 { opr, fst, snd } => Term::Op2 { opr: *opr, fst: Box::new(f(fst)), snd: Box::new(f(snd)) },
      Term::Swi { nam, x, z, s, p } => Term::Swi {
        nam: nam.clone(),
        x: Box::new(f(x)),
        z: Box::new(f(z)),
        s: Box::new(f(s)),
        p: Box::new(f(p)),
      },
      Term::Nat { nat } => Term::Nat { nat: *nat },
      Term::Txt { txt } => Term::Txt { txt: txt.clone() },
      Term::Let { nam, val, bod } => {
        Term::Let { nam: nam.clone(), val: Box::new(f(val)), bod: Box::new(f(bod)) }
      }
      Term::Use { nam, val, bod } => {
        Term::Use { nam: nam.clone(), val: Box::new(f(val)), bod: Box::new(f(bod)) }
      }
      Term::Var { nam } => Term::Var { nam: nam.clone() },
      Term::Hol { nam } => Term::Hol { nam: nam.clone() },
      Term::Met {} => Term::Met {},
      Term::Src { src, val } => Term::Src { src: src.clone(), val: Box::new(f(val)) },
      Term::Mch { mch } => f(&Term::new_match(mch)),
    }
  }

  // TODO: this could be used to implement term equality
  fn rename_variables(t: &Term, i: usize, uses: &Uses) -> Term {
    match t {
      Term::Lam { era, nam, bod } => match uses.get(nam) {
        Some(nam) => Term::Lam {
          era: *era,
          nam: nam.clone(),
          bod: Box::new(rename_variables(bod, i, uses))
        },
        None => {
          let new_nam = format!("x{i}");
          Term::Lam {
            era: *era,
            nam: new_nam.clone(),
            bod: Box::new(rename_variables(bod, i + 1, &uses.update(nam.clone(), new_nam))),
          }
        }
      },
      Term::Var { nam } => Term::Var { nam: uses.get(nam).unwrap_or(nam).clone() },
      _ => apply(t, |t| rename_variables(t, i, uses)),
    }
  }

  #[test]
  /// Test if construction generation matches book
  fn constructor_generation() {
    let book_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("book");
    let modules_to_test = [
      "BBT",
      "BMap",
      "Bool",
      "Char",
      "Cmp",
      "Empty",
      "Equal",
      "List",
      "Maybe",
      "Monad",
      "Nat",
      "Pair",
      "String",
      "Vector",
      "Tests/CtrGen/ParamsTest",
      "Tests/CtrGen/VectorTest",
    ];

    for module in modules_to_test {
      println!("Testing module `{module}`.");
      let mut book = Book::boot(&book_dir.to_string_lossy(), module).unwrap();
      // Needed because some constructors are loaded as ADT.cons instead of ADT/cons
      book.defs = book.defs.into_iter().map(|(key, val)| (key.replace(".", "/"), val)).collect();

      for (_, term) in book.defs.iter() {
        if let Some(adt) = extract_adt(term).as_adt() {
          println!("Testing ADT `{}`.", adt.name);
          let full_name = |adt_name: &str, ctr_name: &str| format!("{adt_name}/{ctr_name}");

          let ctrs: Vec<(&str, &Term)> = adt
            .ctrs
            .iter()
            .map(|ctr| {
              let name = full_name(&adt.name, &ctr.name);
              (ctr.name.as_ref(), book.defs.get(&name).expect(&format!("couldn't find {name}")))
            })
            .collect();

          for (ctr_name, ctr_term) in ctrs {
            println!("Testing constructor {ctr_name}");

            let ctr_ref = full_name(&adt.name, ctr_name);
            let gen_code = Term::constructor_code((&adt.name, term), &ctr_ref).unwrap();
            let gen_term =
              KindParser::new(&gen_code.flatten(None)).parse_def(0, &im::HashMap::new()).unwrap().1;

            let t1 = rename_variables(ctr_term, 0, &im::HashMap::new());
            let t2 = rename_variables(&gen_term, 0, &im::HashMap::new());
            assert_eq!(t1.show(), t2.show());
          }
        }
      }
      println!();
    }
  }
}
