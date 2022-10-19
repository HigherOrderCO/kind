use std::collections::HashMap;
use std::sync::mpsc::Sender;

use kind_report::data::DiagnosticFrame;
use kind_tree::concrete::expr::{Binding, Case, CaseBinding, Destruct};
use kind_tree::concrete::pat::PatIdent;
use kind_tree::concrete::visitor::walk_expr;
use kind_tree::concrete::{Glossary, TopLevel};
use kind_tree::symbol::Ident;

use kind_tree::concrete::{
    expr::{Expr, ExprKind, SttmKind},
    pat::{Pat, PatKind},
    visitor::Visitor,
    Argument, Entry, Rule,
};
use kind_tree::{visit_opt, visit_vec};

use crate::errors::PassError;

pub struct UnboundCollector {
    pub errors: Sender<DiagnosticFrame>,
    pub context_vars: Vec<Ident>,
    pub unbound: HashMap<String, Vec<Ident>>,
}

impl UnboundCollector {
    pub fn new(diagnostic_sender: Sender<DiagnosticFrame>) -> UnboundCollector {
        Self {
            errors: diagnostic_sender,
            context_vars: Default::default(),
            unbound: Default::default(),
        }
    }
}

impl Visitor for UnboundCollector {
    fn visit_attr(&mut self, _: &mut kind_tree::concrete::Attribute) {}

    fn visit_ident(&mut self, ident: &mut Ident) {
        if !self.context_vars.iter().any(|x| x.data == ident.data) {
            let entry = self.unbound.entry(ident.data.0.clone()).or_default();
            entry.push(ident.clone());
        }
    }

    fn visit_pat_ident(&mut self, ident: &mut PatIdent) {
        if let Some(fst) = self.context_vars.iter().find(|x| x.data == ident.0.data) {
            self.errors
                .send(PassError::RepeatedVariable(fst.range, ident.0.range).into())
                .unwrap()
        } else {
            self.context_vars.push(ident.0.clone())
        }
    }

    fn visit_argument(&mut self, argument: &mut Argument) {
        match &mut argument.tipo {
            Some(res) => self.visit_expr(res),
            None => (),
        }
        self.context_vars.push(argument.name.clone());
    }

    fn visit_rule(&mut self, rule: &mut Rule) {
        let vars = self.context_vars.clone();
        for pat in &mut rule.pats {
            self.visit_pat(pat);
        }
        self.visit_expr(&mut rule.body);
        self.context_vars = vars;
    }

    fn visit_entry(&mut self, entry: &mut Entry) {
        let vars = self.context_vars.clone();

        for arg in &mut entry.args.0 {
            self.visit_argument(arg)
        }

        self.visit_expr(&mut entry.tipo);
        self.context_vars = vars;

        for rule in &mut entry.rules {
            self.visit_rule(rule)
        }
    }

    fn visit_top_level(&mut self, toplevel: &mut TopLevel) {
        match toplevel {
            TopLevel::SumType(entr) => {
                self.context_vars.push(entr.name.clone());
                for cons in &entr.constructors {
                    let mut name_cons = cons.name.clone();
                    name_cons.data.0 = format!("{}.{}", name_cons.data.0, cons.name.data.0);
                    self.context_vars.push(name_cons);
                }

                let vars = self.context_vars.clone();

                visit_vec!(&mut entr.parameters.0, arg => self.visit_argument(arg));

                let inside_vars = self.context_vars.clone();

                visit_vec!(&mut entr.indices.0, arg => self.visit_argument(arg));

                visit_vec!(&mut entr.constructors, cons => {
                    self.context_vars = inside_vars.clone();
                    visit_vec!(&mut cons.args.0, arg => self.visit_argument(arg));
                    visit_opt!(&mut cons.tipo, arg => self.visit_expr(arg));
                });

                self.context_vars = vars;
            }
            TopLevel::RecordType(entr) => {
                self.context_vars.push(entr.name.clone());

                let mut name_cons = entr.name.clone();
                name_cons.data.0 = format!("{}.{}", name_cons.data.0, entr.constructor.data.0);
                self.context_vars.push(name_cons);

                let inside_vars = self.context_vars.clone();

                visit_vec!(&mut entr.parameters.0, arg => self.visit_argument(arg));
                visit_vec!(&mut entr.fields, (_, _, typ) => {
                    self.visit_expr(typ);
                });

                self.context_vars = inside_vars;
            }
            TopLevel::Entry(entr) => {
                self.context_vars.push(entr.name.clone());
                self.visit_entry(entr)
            }
        }
    }

    fn visit_book(&mut self, book: &mut kind_tree::concrete::Book) {
        for entr in &mut book.entries {
            self.visit_top_level(entr)
        }
    }

    fn visit_glossary(&mut self, glossary: &mut Glossary) {
        self.context_vars = glossary.names.values().cloned().collect();
        for entr in glossary.entries.values_mut() {
            self.visit_top_level(entr)
        }
    }

    fn visit_destruct(&mut self, destruct: &mut Destruct) {
        match destruct {
            Destruct::Destruct(range, ty, bindings, _) => {
                self.visit_range(range);
                self.visit_ident(ty);
                for bind in bindings {
                    self.visit_case_binding(bind)
                }
            }
            Destruct::Ident(ident) => self.context_vars.push(ident.clone()),
        }
    }

    fn visit_sttm(&mut self, sttm: &mut kind_tree::concrete::expr::Sttm) {
        match &mut sttm.data {
            SttmKind::Ask(ident, val, next) => {
                self.visit_expr(val);
                let vars = self.context_vars.clone();
                self.visit_destruct(ident);
                self.context_vars = vars;
                self.visit_sttm(next);
            }
            SttmKind::Let(ident, val, next) => {
                self.visit_expr(val);
                let vars = self.context_vars.clone();
                self.visit_destruct(ident);
                self.context_vars = vars;
                self.visit_sttm(next);
            }
            SttmKind::Expr(expr, next) => {
                self.visit_expr(expr);
                self.visit_sttm(next);
            }
            SttmKind::Return(expr) => {
                self.visit_expr(expr);
            }
            SttmKind::RetExpr(expr) => {
                self.visit_expr(expr);
            }
        }
    }

    fn visit_pat(&mut self, pat: &mut Pat) {
        match &mut pat.data {
            PatKind::Var(ident) => self.visit_pat_ident(ident),
            PatKind::Str(_) => (),
            PatKind::Num(_) => (),
            PatKind::Hole => (),
            PatKind::List(ls) => {
                for pat in ls {
                    self.visit_pat(pat)
                }
            }
            PatKind::Pair(fst, snd) => {
                self.visit_pat(fst);
                self.visit_pat(snd);
            }
            PatKind::App(t, ls) => {
                self.visit_ident(t);
                for pat in ls {
                    self.visit_pat(pat)
                }
            }
        }
    }

    fn visit_case_binding(&mut self, case_binding: &mut CaseBinding) {
        match case_binding {
            CaseBinding::Field(pat) => self.visit_pat_ident(pat),
            CaseBinding::Renamed(_, pat) => self.visit_pat_ident(pat),
        }
    }

    fn visit_case(&mut self, case: &mut Case) {
        let vars = self.context_vars.clone();
        for binding in &mut case.bindings {
            self.visit_case_binding(binding);
        }
        self.visit_expr(&mut case.value);
        self.context_vars = vars;
    }

    fn visit_match(&mut self, matcher: &mut kind_tree::concrete::expr::Match) {
        self.visit_expr(&mut matcher.scrutinizer);
        for case in &mut matcher.cases {
            // TODO: Better error for not found constructors like this one.
            // let mut name = case.constructor.clone();
            // name.data.0 = format!("{}.{}", matcher.tipo.data.0.clone(), name.data.0);
            // self.visit_ident(&mut name);

            self.visit_case(case);
        }
        match &mut matcher.motive {
            Some(x) => self.visit_expr(x),
            None => (),
        }
    }

    fn visit_binding(&mut self, binding: &mut Binding) {
        match binding {
            Binding::Positional(e) => self.visit_expr(e),
            Binding::Named(_, _, e) => self.visit_expr(e),
        }
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        match &mut expr.data {
            ExprKind::Var(ident) => self.visit_ident(ident),
            ExprKind::Constr(ident) => {
                if !self.context_vars.iter().any(|x| x.data == ident.data) {
                    let entry = self.unbound.entry(ident.data.0.clone()).or_default();
                    entry.push(ident.clone());
                }
            }
            ExprKind::All(Some(ident), typ, body) => {
                self.visit_expr(typ);
                self.context_vars.push(ident.clone());
                self.visit_expr(body);
                self.context_vars.pop();
            }
            ExprKind::Sigma(Some(ident), typ, body) => {
                self.visit_expr(typ);
                self.context_vars.push(ident.clone());
                self.visit_expr(body);
                self.context_vars.pop();
            }
            ExprKind::Lambda(ident, binder, body) => {
                match binder {
                    Some(x) => self.visit_expr(x),
                    None => (),
                }
                self.context_vars.push(ident.clone());
                self.visit_expr(body);
                self.context_vars.pop();
            }
            ExprKind::Let(ident, val, body) => {
                self.visit_expr(val);
                let vars = self.context_vars.clone();
                self.visit_destruct(ident);
                self.visit_expr(body);
                self.context_vars = vars;
            }
            ExprKind::Match(matcher) => self.visit_match(matcher),
            ExprKind::Subst(_subst) => todo!(),
            _ => walk_expr(self, expr),
        }
    }
}