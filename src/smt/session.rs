use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::fs::{File, OpenOptions};
use std::io::{BufRead, Write};

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use crate::{Lit, Model, SolveLimits, Solver, UnknownReason};

use super::arithmetic::rational_from_decimal;
use super::encode::BoolEncoder;
use super::engine::{SmtSolveResult, solve as solve_smt};
use super::proof::{BooleanRefutation, ProofLogic, ProofNames, prove_boolean_unsat};
use super::sexpr::{Reader, SExpr};
use super::term::{
    ArraySortId, FunctionId, Sort, SymbolId, TermId, TermKind, TermStore, TermStoreCheckpoint,
    UninterpretedSortId,
};
use super::theory::{TheoryManager, TheoryModel};

#[derive(Clone, Debug)]
struct Binding {
    term: TermId,
}

#[derive(Clone, Debug)]
enum FunctionBinding {
    Declared(FunctionId),
    Defined {
        parameters: Vec<String>,
        domain: Vec<Sort>,
        range: Sort,
        body: SExpr,
    },
}

#[derive(Clone, Debug)]
struct Declaration {
    name: String,
    term: TermId,
}

#[derive(Clone, Debug)]
struct FunctionDeclaration {
    name: String,
    function: FunctionId,
}

#[derive(Clone, Debug)]
struct NamedAssertion {
    name: String,
    selector: Lit,
}

#[derive(Clone, Debug)]
struct AssignmentLabel {
    name: String,
    term: TermId,
}

#[derive(Clone, Debug)]
struct InlineDefinition {
    name: String,
    term: TermId,
    boolean: bool,
}

#[derive(Clone, Debug)]
struct InlineDefinitionSyntax {
    name: String,
    expression: SExpr,
}

#[derive(Debug)]
struct PreparedCommand {
    command: SExpr,
    definitions: Vec<InlineDefinition>,
    assertion_label: Option<String>,
    term_checkpoint: Option<TermStoreCheckpoint>,
}

#[derive(Debug, Default)]
struct Frame {
    bound_names: Vec<String>,
    bound_functions: Vec<String>,
    bound_sorts: Vec<String>,
    declarations: Vec<Declaration>,
    function_declarations: Vec<FunctionDeclaration>,
    named_assertions: Vec<NamedAssertion>,
    assignment_labels: Vec<AssignmentLabel>,
    assertions: Vec<String>,
    assertion_terms: Vec<TermId>,
}

#[derive(Clone, Debug)]
struct Assumption {
    source: String,
    term: TermId,
    literal: Lit,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum ModelValue {
    Bool(bool),
    BitVec(Vec<bool>),
    Arithmetic(Sort, BigRational),
    Uninterpreted(UninterpretedSortId, u32),
    Array(ArraySortId, u32),
}

#[derive(Clone, Debug)]
enum LastCheck {
    None,
    Sat {
        boolean: Model,
        theory: TheoryModel,
    },
    Unsat {
        core: Vec<String>,
        assumptions: Vec<String>,
        proof: Option<BooleanRefutation>,
    },
    Unknown {
        reason: UnknownReason,
        boolean: Model,
        theory: TheoryModel,
    },
}

#[derive(Clone, Debug, Default)]
struct Options {
    print_success: bool,
    produce_models: bool,
    produce_assignments: bool,
    produce_assertions: bool,
    produce_unsat_cores: bool,
    produce_unsat_assumptions: bool,
    produce_proofs: bool,
    global_declarations: bool,
    resource_limit: Option<u64>,
    regular_output_channel: Option<String>,
    diagnostic_output_channel: Option<String>,
}

/// A persistent SMT-LIB session for the currently implemented Core-Boolean
/// fragment.
#[derive(Debug)]
pub struct Session {
    terms: TermStore,
    solver: Solver,
    encoder: BoolEncoder,
    theories: TheoryManager,
    bindings: HashMap<String, Binding>,
    functions: HashMap<String, FunctionBinding>,
    sorts: HashMap<String, Sort>,
    sort_names: HashMap<UninterpretedSortId, String>,
    frames: Vec<Frame>,
    logic: Option<String>,
    options: Options,
    last_check: LastCheck,
    exited: bool,
}

impl Default for Session {
    fn default() -> Self {
        Self::new()
    }
}

impl Session {
    #[must_use]
    pub fn new() -> Self {
        Self {
            terms: TermStore::new(),
            solver: Solver::new(),
            encoder: BoolEncoder::default(),
            theories: TheoryManager::default(),
            bindings: HashMap::new(),
            functions: HashMap::new(),
            sorts: HashMap::new(),
            sort_names: HashMap::new(),
            frames: vec![Frame::default()],
            logic: None,
            options: Options::default(),
            last_check: LastCheck::None,
            exited: false,
        }
    }

    /// Executes one already-parsed top-level command.
    pub(crate) fn execute(&mut self, command: &SExpr) -> CommandOutput {
        if self.exited {
            return CommandOutput::error("command issued after exit");
        }
        let PreparedCommand {
            command: stripped,
            definitions,
            assertion_label,
            term_checkpoint,
        } = match self.prepare_inline_definitions(command) {
            Ok(prepared) => prepared,
            Err(CommandError::Unsupported) => return CommandOutput::text("unsupported"),
            Err(CommandError::Message(message)) => return CommandOutput::error(&message),
        };
        let result = self.execute_inner(&stripped, command, assertion_label.as_deref());
        if result.is_ok() {
            self.commit_inline_definitions(&definitions);
        } else {
            self.rollback_inline_definitions(&definitions);
            if let Some(checkpoint) = term_checkpoint {
                self.terms.rollback(checkpoint);
            }
        }
        match result {
            Ok(CommandValue::Success) => {
                if self.options.print_success {
                    CommandOutput::text("success")
                } else {
                    CommandOutput::silent()
                }
            }
            Ok(CommandValue::Text(text)) => CommandOutput::text(text),
            Ok(CommandValue::Exit) => {
                self.exited = true;
                CommandOutput {
                    response: self.options.print_success.then(|| "success".to_owned()),
                    exit: true,
                }
            }
            Err(CommandError::Unsupported) => CommandOutput::text("unsupported"),
            Err(CommandError::Message(message)) => CommandOutput::error(&message),
        }
    }

    fn execute_inner(
        &mut self,
        command: &SExpr,
        original: &SExpr,
        assertion_label: Option<&str>,
    ) -> Result<CommandValue, CommandError> {
        let items = expect_list(command, "top-level command")?;
        let Some((head, arguments)) = items.split_first() else {
            return Err(CommandError::message("empty command"));
        };
        let original_items = expect_list(original, "top-level command")?;
        let Some((_, original_arguments)) = original_items.split_first() else {
            return Err(CommandError::message("empty command"));
        };
        let name = expect_word(head, "command name")?;
        match name {
            "set-logic" => self.set_logic(arguments),
            "set-option" => self.set_option(arguments),
            "get-option" => self.get_option(arguments),
            "set-info" => self.set_info(arguments),
            "get-info" => self.get_info(arguments),
            "declare-sort" => self.declare_sort(arguments),
            "define-sort" => self.define_sort(arguments),
            "declare-const" => self.declare_const(arguments),
            "declare-fun" => self.declare_fun(arguments),
            "define-const" => self.define_const(arguments),
            "define-fun" => self.define_fun(arguments),
            "assert" => self.assert(arguments, original_arguments, assertion_label),
            "push" => self.push(arguments),
            "pop" => self.pop(arguments),
            "check-sat" => self.check_sat(arguments),
            "check-sat-assuming" => self.check_sat_assuming(arguments),
            "get-model" => self.get_model(arguments),
            "get-value" => self.get_value(arguments),
            "get-assignment" => self.get_assignment(arguments),
            "get-assertions" => self.get_assertions(arguments),
            "get-unsat-core" => self.get_unsat_core(arguments),
            "get-unsat-assumptions" => self.get_unsat_assumptions(arguments),
            "get-proof" => self.get_proof(arguments),
            "reset-assertions" => self.reset_assertions(arguments),
            "reset" => self.reset(arguments),
            "echo" => self.echo(arguments),
            "exit" => {
                expect_arity(arguments, 0, "exit")?;
                Ok(CommandValue::Exit)
            }
            "declare-datatype"
            | "declare-datatypes"
            | "declare-sort-parameter"
            | "define-fun-rec"
            | "define-funs-rec" => Err(CommandError::Unsupported),
            _ => Err(CommandError::message(format!(
                "unsupported command `{name}`"
            ))),
        }
    }

    fn set_logic(&mut self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 1, "set-logic")?;
        if self.logic.is_some() {
            return Err(CommandError::message("logic has already been set"));
        }
        let logic = expect_symbol(&arguments[0], "logic name")?;
        if !matches!(
            logic,
            "ALL"
                | "QF_BOOL"
                | "QF_BV"
                | "QF_UF"
                | "QF_UFBV"
                | "QF_ABV"
                | "QF_AUFBV"
                | "QF_IDL"
                | "QF_LIA"
                | "QF_RDL"
                | "QF_LRA"
                | "QF_UFIDL"
                | "QF_UFLIA"
                | "QF_UFLRA"
                | "QF_AUFLIA"
        ) {
            return Err(CommandError::Unsupported);
        }
        if self.options.produce_proofs && ProofLogic::from_name(logic).is_none() {
            return Err(CommandError::Unsupported);
        }
        self.logic = Some(logic.to_owned());
        Ok(CommandValue::Success)
    }

    fn set_option(&mut self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 2, "set-option")?;
        let option = expect_keyword(&arguments[0], "option name")?;
        match option {
            ":print-success" => {
                self.options.print_success = expect_bool_atom(&arguments[1], option)?;
            }
            ":produce-models" => {
                self.require_start_mode(option)?;
                self.options.produce_models = expect_bool_atom(&arguments[1], option)?;
            }
            ":produce-assignments" => {
                self.require_start_mode(option)?;
                self.options.produce_assignments = expect_bool_atom(&arguments[1], option)?;
            }
            ":produce-assertions" | ":interactive-mode" => {
                self.require_start_mode(option)?;
                self.options.produce_assertions = expect_bool_atom(&arguments[1], option)?;
            }
            ":produce-unsat-cores" => {
                self.require_start_mode(option)?;
                self.options.produce_unsat_cores = expect_bool_atom(&arguments[1], option)?;
            }
            ":produce-unsat-assumptions" => {
                self.require_start_mode(option)?;
                self.options.produce_unsat_assumptions = expect_bool_atom(&arguments[1], option)?;
            }
            ":produce-proofs" => {
                self.require_start_mode(option)?;
                self.options.produce_proofs = expect_bool_atom(&arguments[1], option)?;
            }
            ":global-declarations" => {
                self.require_start_mode(option)?;
                self.options.global_declarations = expect_bool_atom(&arguments[1], option)?;
            }
            ":regular-output-channel" => {
                let channel = expect_string(&arguments[1], option)?;
                self.options.regular_output_channel =
                    (channel != "stdout").then(|| channel.to_owned());
            }
            ":diagnostic-output-channel" => {
                let channel = expect_string(&arguments[1], option)?;
                self.options.diagnostic_output_channel =
                    (channel != "stderr").then(|| channel.to_owned());
            }
            ":reproducible-resource-limit" => {
                let value = parse_usize(&arguments[1], option)?;
                self.options.resource_limit =
                    (value != 0).then_some(u64::try_from(value).unwrap_or(u64::MAX));
            }
            _ => return Err(CommandError::Unsupported),
        }
        Ok(CommandValue::Success)
    }

    fn get_option(&self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 1, "get-option")?;
        let option = expect_keyword(&arguments[0], "option name")?;
        let value = match option {
            ":print-success" => bool_text(self.options.print_success),
            ":produce-models" => bool_text(self.options.produce_models),
            ":produce-assignments" => bool_text(self.options.produce_assignments),
            ":produce-assertions" | ":interactive-mode" => {
                bool_text(self.options.produce_assertions)
            }
            ":produce-unsat-cores" => bool_text(self.options.produce_unsat_cores),
            ":produce-unsat-assumptions" => bool_text(self.options.produce_unsat_assumptions),
            ":produce-proofs" => bool_text(self.options.produce_proofs),
            ":global-declarations" => bool_text(self.options.global_declarations),
            ":regular-output-channel" => {
                return Ok(CommandValue::Text(quote_string(
                    self.regular_output_channel(),
                )));
            }
            ":diagnostic-output-channel" => {
                return Ok(CommandValue::Text(quote_string(
                    self.diagnostic_output_channel(),
                )));
            }
            ":reproducible-resource-limit" => {
                return Ok(CommandValue::Text(
                    self.options.resource_limit.unwrap_or(0).to_string(),
                ));
            }
            ":random-seed" => "0",
            _ => return Err(CommandError::Unsupported),
        };
        Ok(CommandValue::Text(value.to_owned()))
    }

    fn set_info(&self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        if !(1..=2).contains(&arguments.len()) {
            return Err(CommandError::message(format!(
                "`set-info` expects an attribute, received {} arguments",
                arguments.len()
            )));
        }
        expect_keyword(&arguments[0], "information attribute")?;
        Ok(CommandValue::Success)
    }

    fn get_info(&self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 1, "get-info")?;
        let flag = expect_keyword(&arguments[0], "information flag")?;
        let text = match flag {
            ":name" => "(:name \"sat SMT\")".to_owned(),
            ":version" => format!("(:version \"{}\")", env!("CARGO_PKG_VERSION")),
            ":authors" => "(:authors \"sat contributors\")".to_owned(),
            ":assertion-stack-levels" => {
                format!("(:assertion-stack-levels {})", self.frames.len() - 1)
            }
            ":status" => {
                let status = match self.last_check {
                    LastCheck::None => "unknown",
                    LastCheck::Sat { .. } => "sat",
                    LastCheck::Unsat { .. } => "unsat",
                    LastCheck::Unknown { .. } => "unknown",
                };
                format!("(:status {status})")
            }
            ":error-behavior" => "(:error-behavior continued-execution)".to_owned(),
            ":reason-unknown" => {
                let LastCheck::Unknown { reason, .. } = self.last_check else {
                    return Err(CommandError::message(
                        "reason-unknown requires a preceding unknown result",
                    ));
                };
                let reason = match reason {
                    UnknownReason::Interrupted => "interrupted",
                    UnknownReason::ConflictLimit | UnknownReason::PropagationLimit => "resourceout",
                    UnknownReason::IncompleteTheory => "incomplete",
                    UnknownReason::ModelValidationFailure => "model-validation-failure",
                };
                format!("(:reason-unknown {reason})")
            }
            _ => return Err(CommandError::Unsupported),
        };
        Ok(CommandValue::Text(text))
    }

    fn declare_sort(&mut self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 2, "declare-sort")?;
        self.require_uf()?;
        let name = expect_symbol(&arguments[0], "sort name")?.to_owned();
        self.ensure_fresh_sort_name(&name)?;
        let arity = parse_usize(&arguments[1], "sort arity")?;
        if arity != 0 {
            return Err(CommandError::Unsupported);
        }
        let id = self
            .terms
            .fresh_uninterpreted_sort()
            .map_err(CommandError::from)?;
        let sort = Sort::Uninterpreted(id);
        self.sorts.insert(name.clone(), sort);
        self.sort_names.entry(id).or_insert_with(|| name.clone());
        let target = self.declaration_frame();
        self.frames[target].bound_sorts.push(name);
        self.invalidate_check();
        Ok(CommandValue::Success)
    }

    fn define_sort(&mut self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 3, "define-sort")?;
        self.require_logic()?;
        let name = expect_symbol(&arguments[0], "sort name")?.to_owned();
        self.ensure_fresh_sort_name(&name)?;
        let parameters = expect_list(&arguments[1], "sort parameters")?;
        if !parameters.is_empty() {
            return Err(CommandError::Unsupported);
        }
        let checkpoint = self.terms.checkpoint();
        let sort = match self.parse_sort(&arguments[2]) {
            Ok(sort) => sort,
            Err(error) => {
                self.terms.rollback(checkpoint);
                return Err(error);
            }
        };
        self.sorts.insert(name.clone(), sort);
        let target = self.declaration_frame();
        self.frames[target].bound_sorts.push(name);
        self.invalidate_check();
        Ok(CommandValue::Success)
    }

    fn declare_const(&mut self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 2, "declare-const")?;
        let name = expect_symbol(&arguments[0], "constant name")?.to_owned();
        let checkpoint = self.terms.checkpoint();
        let result = (|| {
            let sort = self.parse_sort(&arguments[1])?;
            self.declare_term(name, sort)
        })();
        self.finish_term_transaction(checkpoint, result)
    }

    fn declare_fun(&mut self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 3, "declare-fun")?;
        let name = expect_symbol(&arguments[0], "function name")?.to_owned();
        let checkpoint = self.terms.checkpoint();
        let result = (|| {
            let parameters = expect_list(&arguments[1], "function parameter sorts")?;
            let domain = parameters
                .iter()
                .map(|parameter| self.parse_sort(parameter))
                .collect::<Result<Vec<_>, _>>()?;
            let range = self.parse_sort(&arguments[2])?;
            if domain.is_empty() {
                return self.declare_term(name, range);
            }
            self.require_uf()?;
            self.ensure_fresh_name(&name)?;
            let function = self
                .terms
                .declare_function(&domain, range)
                .map_err(CommandError::from)?;
            self.functions
                .insert(name.clone(), FunctionBinding::Declared(function));
            let target = self.declaration_frame();
            self.frames[target].bound_functions.push(name.clone());
            self.frames[target]
                .function_declarations
                .push(FunctionDeclaration { name, function });
            self.invalidate_check();
            Ok(CommandValue::Success)
        })();
        self.finish_term_transaction(checkpoint, result)
    }

    fn declare_term(&mut self, name: String, sort: Sort) -> Result<CommandValue, CommandError> {
        self.require_logic()?;
        self.ensure_fresh_name(&name)?;
        let term = self.terms.fresh_term(sort).map_err(CommandError::from)?;
        self.bindings.insert(name.clone(), Binding { term });
        let target = self.declaration_frame();
        self.frames[target].bound_names.push(name.clone());
        self.frames[target]
            .declarations
            .push(Declaration { name, term });
        self.invalidate_check();
        Ok(CommandValue::Success)
    }

    fn define_const(&mut self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 3, "define-const")?;
        let name = expect_symbol(&arguments[0], "constant name")?.to_owned();
        let checkpoint = self.terms.checkpoint();
        let result = (|| {
            let sort = self.parse_sort(&arguments[1])?;
            let term = self.parse_term(&arguments[2], &[])?;
            self.define_term(name, sort, term)
        })();
        self.finish_term_transaction(checkpoint, result)
    }

    fn define_fun(&mut self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 4, "define-fun")?;
        let name = expect_symbol(&arguments[0], "function name")?.to_owned();
        let command_checkpoint = self.terms.checkpoint();
        let result = (|| {
            let parameters = expect_list(&arguments[1], "function parameters")?;
            let mut names = HashSet::new();
            let mut parameter_names = Vec::with_capacity(parameters.len());
            let mut domain = Vec::with_capacity(parameters.len());
            for parameter in parameters {
                let fields = expect_list(parameter, "function parameter")?;
                expect_arity(fields, 2, "function parameter")?;
                let parameter_name = expect_symbol(&fields[0], "parameter name")?.to_owned();
                if !names.insert(parameter_name.clone()) {
                    return Err(CommandError::message(format!(
                        "duplicate function parameter `{parameter_name}`"
                    )));
                }
                parameter_names.push(parameter_name);
                domain.push(self.parse_sort(&fields[1])?);
            }
            let range = self.parse_sort(&arguments[2])?;
            if domain.is_empty() {
                let term = self.parse_term(&arguments[3], &[])?;
                return self.define_term(name, range, term);
            }
            self.require_uf()?;
            self.ensure_fresh_name(&name)?;
            // Parameter placeholders exist only to sort-check the macro body.
            // Roll them back so neither a rejected definition nor a successful
            // one consumes persistent symbols or model values.
            let body_checkpoint = self.terms.checkpoint();
            let body_sort = (|| {
                let mut locals = HashMap::new();
                for (&sort, parameter) in domain.iter().zip(parameter_names.iter()) {
                    let term = self.terms.fresh_term(sort).map_err(CommandError::from)?;
                    locals.insert(parameter.clone(), term);
                }
                let body_term = self.parse_term(&arguments[3], &[locals])?;
                self.terms.sort(body_term).map_err(CommandError::from)
            })();
            self.terms.rollback(body_checkpoint);
            if body_sort? != range {
                return Err(CommandError::message(format!(
                    "definition of `{name}` does not have its declared result sort"
                )));
            }
            self.functions.insert(
                name.clone(),
                FunctionBinding::Defined {
                    parameters: parameter_names,
                    domain,
                    range,
                    body: arguments[3].clone(),
                },
            );
            let target = self.declaration_frame();
            self.frames[target].bound_functions.push(name);
            self.invalidate_check();
            Ok(CommandValue::Success)
        })();
        self.finish_term_transaction(command_checkpoint, result)
    }

    fn define_term(
        &mut self,
        name: String,
        sort: Sort,
        term: TermId,
    ) -> Result<CommandValue, CommandError> {
        self.require_logic()?;
        self.ensure_fresh_name(&name)?;
        if self.terms.sort(term).map_err(CommandError::from)? != sort {
            return Err(CommandError::message(format!(
                "definition of `{name}` does not have its declared sort"
            )));
        }
        self.bindings.insert(name.clone(), Binding { term });
        let target = self.declaration_frame();
        self.frames[target].bound_names.push(name);
        self.invalidate_check();
        Ok(CommandValue::Success)
    }

    fn assert(
        &mut self,
        arguments: &[SExpr],
        original_arguments: &[SExpr],
        name: Option<&str>,
    ) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 1, "assert")?;
        expect_arity(original_arguments, 1, "assert")?;
        self.require_logic()?;
        let checkpoint = self.terms.checkpoint();
        let term = match self.parse_term(&arguments[0], &[]).and_then(|term| {
            self.terms.require_bool(term).map_err(CommandError::from)?;
            Ok(term)
        }) {
            Ok(term) => term,
            Err(error) => {
                self.terms.rollback(checkpoint);
                return Err(error);
            }
        };
        let literal = self
            .encoder
            .encode(&self.terms, &mut self.solver, term)
            .map_err(CommandError::from)?;
        let rendered = render(&original_arguments[0]);
        if let Some(name) = name {
            let definition = self
                .bindings
                .get(name)
                .ok_or_else(|| CommandError::message("missing inline assertion label"))?;
            if definition.term != term {
                return Err(CommandError::message(
                    "inline assertion label does not name the asserted term",
                ));
            }
            let selector = Lit::positive(self.solver.new_variable().map_err(CommandError::from)?);
            self.solver
                .try_add_clause(&[!selector, literal])
                .map_err(CommandError::from)?;
            self.frames
                .last_mut()
                .expect("base frame exists")
                .named_assertions
                .push(NamedAssertion {
                    name: name.to_owned(),
                    selector,
                });
        } else {
            self.solver
                .try_add_clause(&[literal])
                .map_err(CommandError::from)?;
        }
        let frame = self.frames.last_mut().expect("base frame exists");
        frame.assertions.push(rendered);
        frame.assertion_terms.push(term);
        self.invalidate_check();
        Ok(CommandValue::Success)
    }

    fn push(&mut self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 1, "push")?;
        self.require_logic()?;
        let levels = parse_usize(&arguments[0], "push level count")?;
        self.solver
            .check_push_levels(levels)
            .map_err(CommandError::from)?;
        self.frames
            .try_reserve(levels)
            .map_err(|_| CommandError::from(crate::IncrementalError::ResourceExhausted))?;
        self.solver
            .push_levels(levels)
            .map_err(CommandError::from)?;
        self.frames.extend((0..levels).map(|_| Frame::default()));
        self.invalidate_check();
        Ok(CommandValue::Success)
    }

    fn pop(&mut self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 1, "pop")?;
        self.require_logic()?;
        let levels = parse_usize(&arguments[0], "pop level count")?;
        if levels >= self.frames.len() {
            return Err(CommandError::message("cannot pop beyond the base scope"));
        }
        self.solver.pop(levels).map_err(CommandError::from)?;
        for _ in 0..levels {
            let frame = self.frames.pop().expect("scope count checked above");
            for name in frame.bound_names {
                self.bindings.remove(&name);
            }
            for name in frame.bound_functions {
                self.functions.remove(&name);
            }
            for name in frame.bound_sorts {
                self.sorts.remove(&name);
            }
        }
        self.invalidate_check();
        Ok(CommandValue::Success)
    }

    fn check_sat(&mut self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 0, "check-sat")?;
        self.run_check(&[])
    }

    fn check_sat_assuming(&mut self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 1, "check-sat-assuming")?;
        let expressions = expect_list(&arguments[0], "assumption list")?;
        let checkpoint = self.terms.checkpoint();
        let mut parsed = Vec::with_capacity(expressions.len());
        for expression in expressions {
            let term = match self.parse_term(expression, &[]) {
                Ok(term) => term,
                Err(error) => {
                    self.terms.rollback(checkpoint);
                    return Err(error);
                }
            };
            if let Err(error) = self.terms.require_bool(term) {
                self.terms.rollback(checkpoint);
                return Err(CommandError::from(error));
            }
            parsed.push((render(expression), term));
        }

        // Validate every assumption before lowering any of them. Encoding is a
        // persistent, conservative extension of the SAT state, so installing a
        // valid prefix before a later malformed assumption would make an
        // error-generating command observably affect subsequent deterministic
        // checks.
        let mut assumptions = Vec::with_capacity(parsed.len());
        for (source, term) in parsed {
            let literal = self
                .encoder
                .encode(&self.terms, &mut self.solver, term)
                .map_err(CommandError::from)?;
            assumptions.push(Assumption {
                source,
                term,
                literal,
            });
        }
        self.run_check(&assumptions)
    }

    fn run_check(&mut self, user_assumptions: &[Assumption]) -> Result<CommandValue, CommandError> {
        self.require_logic()?;
        let named = self
            .frames
            .iter()
            .flat_map(|frame| frame.named_assertions.iter())
            .cloned()
            .collect::<Vec<_>>();
        let mut assumptions = named
            .iter()
            .map(|assertion| assertion.selector)
            .collect::<Vec<_>>();
        assumptions.extend(user_assumptions.iter().map(|assumption| assumption.literal));
        let mut roots = self
            .frames
            .iter()
            .flat_map(|frame| frame.assertion_terms.iter().copied())
            .collect::<Vec<_>>();
        roots.extend(user_assumptions.iter().map(|assumption| assumption.term));
        let proof_logic = self.options.produce_proofs.then(|| {
            ProofLogic::from_name(
                self.logic
                    .as_deref()
                    .expect("run_check requires a selected logic"),
            )
            .expect("set_logic rejects proof-unsupported logics")
        });
        let proof_premises = (proof_logic.is_some() && user_assumptions.is_empty()).then(|| {
            self.frames
                .iter()
                .flat_map(|frame| frame.assertions.iter().cloned())
                .collect::<Vec<_>>()
        });
        let result = solve_smt(
            &mut self.terms,
            &mut self.solver,
            &mut self.encoder,
            &mut self.theories,
            &roots,
            &assumptions,
            SolveLimits {
                conflicts: self.options.resource_limit,
                propagations: None,
            },
        )
        .map_err(CommandError::from)?;
        let text = match result {
            SmtSolveResult::Sat { boolean, theory } => {
                self.last_check = LastCheck::Sat { boolean, theory };
                "sat"
            }
            SmtSolveResult::Unsat => {
                let proof = if let Some(premises) = proof_premises.as_deref() {
                    let names = self.active_proof_names()?;
                    Some(
                        prove_boolean_unsat(
                            proof_logic.expect("proof premises require a proof logic"),
                            &self.terms,
                            &roots,
                            premises,
                            &names,
                        )
                        .map_err(CommandError::from)?,
                    )
                } else {
                    None
                };
                let failed = self.solver.failed_assumptions();
                let core = named
                    .iter()
                    .filter(|assertion| failed.contains(&assertion.selector))
                    .map(|assertion| assertion.name.clone())
                    .collect();
                let assumptions = user_assumptions
                    .iter()
                    .filter(|assumption| failed.contains(&assumption.literal))
                    .map(|assumption| assumption.source.clone())
                    .collect();
                self.last_check = LastCheck::Unsat {
                    core,
                    assumptions,
                    proof,
                };
                "unsat"
            }
            SmtSolveResult::Unknown(reason) => {
                self.last_check = LastCheck::Unknown {
                    reason,
                    boolean: self.solver.arbitrary_model(),
                    theory: TheoryModel::default(),
                };
                "unknown"
            }
        };
        Ok(CommandValue::Text(text.to_owned()))
    }

    fn get_model(&self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 0, "get-model")?;
        if !self.options.produce_models {
            return Err(CommandError::message(
                "model production is disabled; set :produce-models true",
            ));
        }
        let model = self.sat_model()?;
        let theory = self.sat_theory_model()?;
        let mut definitions = Vec::new();
        for declaration in self.active_declarations() {
            let sort = self
                .terms
                .sort(declaration.term)
                .map_err(CommandError::from)?;
            let value = self.render_term_value(model, theory, declaration.term)?;
            definitions.push(format!(
                "(define-fun {} () {} {})",
                quote_symbol(&declaration.name),
                self.render_sort(sort),
                value
            ));
        }
        for declaration in self.active_function_declarations() {
            definitions.push(self.render_function_model(model, theory, declaration)?);
        }
        if definitions.is_empty() {
            Ok(CommandValue::Text("()".to_owned()))
        } else {
            Ok(CommandValue::Text(format!(
                "(\n  {}\n)",
                definitions.join("\n  ")
            )))
        }
    }

    fn get_value(&mut self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 1, "get-value")?;
        if !self.options.produce_models {
            return Err(CommandError::message(
                "model production is disabled; set :produce-models true",
            ));
        }
        let expressions = expect_list(&arguments[0], "get-value term list")?;
        if expressions.is_empty() {
            return Err(CommandError::message("get-value expects at least one term"));
        }
        let model = self.sat_model()?.clone();
        let theory = self.sat_theory_model()?.clone();
        let checkpoint = self.terms.checkpoint();
        let result = (|| {
            let mut values = Vec::with_capacity(expressions.len());
            for expression in expressions {
                let term = self.parse_term(expression, &[])?;
                let value = self.render_term_value(&model, &theory, term)?;
                values.push(format!("({} {value})", render(expression)));
            }
            Ok(CommandValue::Text(format!("({})", values.join(" "))))
        })();
        self.terms.rollback(checkpoint);
        result
    }

    fn get_assignment(&self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 0, "get-assignment")?;
        if !self.options.produce_assignments {
            return Err(CommandError::message(
                "assignment production is disabled; set :produce-assignments true",
            ));
        }
        let model = self.sat_model()?;
        let assignments = self
            .frames
            .iter()
            .flat_map(|frame| frame.assignment_labels.iter())
            .map(|label| {
                format!(
                    "({} {})",
                    quote_symbol(&label.name),
                    bool_text(self.bool_term_value(model, label.term))
                )
            })
            .collect::<Vec<_>>();
        Ok(CommandValue::Text(format!("({})", assignments.join(" "))))
    }

    fn get_assertions(&self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 0, "get-assertions")?;
        self.require_logic()?;
        if !self.options.produce_assertions {
            return Err(CommandError::message(
                "assertion production is disabled; set :produce-assertions true",
            ));
        }
        let assertions = self
            .frames
            .iter()
            .flat_map(|frame| frame.assertions.iter().cloned())
            .collect::<Vec<_>>();
        Ok(CommandValue::Text(format!("({})", assertions.join(" "))))
    }

    fn get_unsat_core(&self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 0, "get-unsat-core")?;
        if !self.options.produce_unsat_cores {
            return Err(CommandError::message(
                "unsat-core production is disabled; set :produce-unsat-cores true",
            ));
        }
        let LastCheck::Unsat { core, .. } = &self.last_check else {
            return Err(CommandError::message(
                "get-unsat-core requires a preceding unsat result",
            ));
        };
        let core = core
            .iter()
            .map(|name| quote_symbol(name))
            .collect::<Vec<_>>();
        Ok(CommandValue::Text(format!("({})", core.join(" "))))
    }

    fn get_unsat_assumptions(&self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 0, "get-unsat-assumptions")?;
        if !self.options.produce_unsat_assumptions {
            return Err(CommandError::message(
                "unsat-assumption production is disabled; \
                 set :produce-unsat-assumptions true",
            ));
        }
        let LastCheck::Unsat { assumptions, .. } = &self.last_check else {
            return Err(CommandError::message(
                "get-unsat-assumptions requires a preceding unsat result",
            ));
        };
        Ok(CommandValue::Text(format!("({})", assumptions.join(" "))))
    }

    fn get_proof(&self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 0, "get-proof")?;
        if !self.options.produce_proofs {
            return Err(CommandError::message(
                "proof production is disabled; set :produce-proofs true",
            ));
        }
        let LastCheck::Unsat { proof, .. } = &self.last_check else {
            return Err(CommandError::message(
                "get-proof requires a preceding unsat result",
            ));
        };
        let Some(proof) = proof else {
            return Err(CommandError::message(
                "get-proof requires the preceding check to have an empty assumption set",
            ));
        };
        Ok(CommandValue::Text(proof.render()))
    }

    fn reset_assertions(&mut self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 0, "reset-assertions")?;
        if self.options.global_declarations {
            let declarations = self.active_declarations().cloned().collect::<Vec<_>>();
            let function_declarations = self
                .active_function_declarations()
                .cloned()
                .collect::<Vec<_>>();
            let assignment_labels = self
                .frames
                .iter()
                .flat_map(|frame| frame.assignment_labels.iter().cloned())
                .collect();
            let names = self.bindings.clone();
            let functions = self.functions.clone();
            let sorts = self.sorts.clone();
            self.frames.clear();
            self.frames.push(Frame {
                bound_names: names.keys().cloned().collect(),
                bound_functions: functions.keys().cloned().collect(),
                bound_sorts: sorts.keys().cloned().collect(),
                declarations,
                function_declarations,
                assignment_labels,
                ..Frame::default()
            });
        } else {
            self.terms = TermStore::new();
            self.bindings.clear();
            self.functions.clear();
            self.sorts.clear();
            self.sort_names.clear();
            self.frames.clear();
            self.frames.push(Frame::default());
        }
        self.solver = Solver::new();
        self.encoder = BoolEncoder::default();
        self.theories = TheoryManager::default();
        self.invalidate_check();
        Ok(CommandValue::Success)
    }

    fn reset(&mut self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 0, "reset")?;
        *self = Self::new();
        Ok(CommandValue::Success)
    }

    fn echo(&self, arguments: &[SExpr]) -> Result<CommandValue, CommandError> {
        expect_arity(arguments, 1, "echo")?;
        let value = expect_string(&arguments[0], "echo argument")?;
        Ok(CommandValue::Text(quote_string(value)))
    }

    fn regular_output_channel(&self) -> &str {
        self.options
            .regular_output_channel
            .as_deref()
            .unwrap_or("stdout")
    }

    fn diagnostic_output_channel(&self) -> &str {
        self.options
            .diagnostic_output_channel
            .as_deref()
            .unwrap_or("stderr")
    }

    fn restore_regular_output_channel(&mut self, channel: String) {
        self.options.regular_output_channel = (channel != "stdout").then_some(channel);
    }

    fn restore_diagnostic_output_channel(&mut self, channel: String) {
        self.options.diagnostic_output_channel = (channel != "stderr").then_some(channel);
    }

    fn prepare_inline_definitions(
        &mut self,
        command: &SExpr,
    ) -> Result<PreparedCommand, CommandError> {
        let (command, syntax, assertion_label) = strip_inline_definitions(command)?;
        let term_checkpoint = (!syntax.is_empty()).then(|| self.terms.checkpoint());
        let mut names = HashSet::new();
        for definition in &syntax {
            self.ensure_fresh_name(&definition.name)?;
            if !names.insert(definition.name.clone()) {
                return Err(CommandError::message(format!(
                    "inline label `{}` is repeated in the command",
                    definition.name
                )));
            }
        }

        let mut definitions = Vec::with_capacity(syntax.len());
        for definition in syntax {
            let term = match self.parse_term(&definition.expression, &[]) {
                Ok(term) => term,
                Err(error) => {
                    self.rollback_inline_definitions(&definitions);
                    if let Some(checkpoint) = term_checkpoint {
                        self.terms.rollback(checkpoint);
                    }
                    return Err(error);
                }
            };
            let boolean = match self.terms.sort(term) {
                Ok(sort) => sort == Sort::Bool,
                Err(error) => {
                    self.rollback_inline_definitions(&definitions);
                    if let Some(checkpoint) = term_checkpoint {
                        self.terms.rollback(checkpoint);
                    }
                    return Err(CommandError::from(error));
                }
            };
            self.bindings
                .insert(definition.name.clone(), Binding { term });
            definitions.push(InlineDefinition {
                name: definition.name,
                term,
                boolean,
            });
        }

        Ok(PreparedCommand {
            command,
            definitions,
            assertion_label,
            term_checkpoint,
        })
    }

    fn commit_inline_definitions(&mut self, definitions: &[InlineDefinition]) {
        if definitions.is_empty() {
            return;
        }
        let target = self.declaration_frame();
        for definition in definitions {
            self.frames[target]
                .bound_names
                .push(definition.name.clone());
            if definition.boolean {
                self.frames[target].assignment_labels.push(AssignmentLabel {
                    name: definition.name.clone(),
                    term: definition.term,
                });
            }
        }
    }

    fn rollback_inline_definitions(&mut self, definitions: &[InlineDefinition]) {
        for definition in definitions {
            self.bindings.remove(&definition.name);
        }
    }

    fn finish_term_transaction<T>(
        &mut self,
        checkpoint: TermStoreCheckpoint,
        result: Result<T, CommandError>,
    ) -> Result<T, CommandError> {
        if result.is_err() {
            self.terms.rollback(checkpoint);
        }
        result
    }

    fn parse_term(
        &mut self,
        expression: &SExpr,
        locals: &[HashMap<String, TermId>],
    ) -> Result<TermId, CommandError> {
        if let Some(literal) = expression.binary() {
            self.require_bitvectors()?;
            return self
                .terms
                .bitvec_from_binary(literal)
                .map_err(CommandError::from);
        }
        if let Some(literal) = expression.hexadecimal() {
            self.require_bitvectors()?;
            return self
                .terms
                .bitvec_from_hexadecimal(literal)
                .map_err(CommandError::from);
        }
        if let Some(numeral) = expression.numeral() {
            self.require_arithmetic()?;
            let value = BigInt::parse_bytes(numeral.as_bytes(), 10)
                .ok_or_else(|| CommandError::message("invalid integer numeral"))?;
            return self
                .terms
                .arithmetic_integer(value)
                .map_err(CommandError::from);
        }
        if let Some(decimal) = expression.decimal() {
            self.require_arithmetic()?;
            let value = rational_from_decimal(decimal)
                .ok_or_else(|| CommandError::message("invalid real decimal"))?;
            return self
                .terms
                .arithmetic_real(value)
                .map_err(CommandError::from);
        }
        if let Some(symbol) = expression.symbol() {
            return match symbol {
                "true" => Ok(self.terms.bool_constant(true)),
                "false" => Ok(self.terms.bool_constant(false)),
                _ => locals
                    .iter()
                    .rev()
                    .find_map(|scope| scope.get(symbol).copied())
                    .or_else(|| self.bindings.get(symbol).map(|binding| binding.term))
                    .ok_or_else(|| CommandError::message(format!("unknown symbol `{symbol}`"))),
            };
        }
        let items = expect_list(expression, "term application")?;
        let Some((head, arguments)) = items.split_first() else {
            return Err(CommandError::message("empty term application"));
        };
        if head.word() == Some("_") {
            return self.parse_indexed_constant(items);
        }
        if let SExpr::List(identifier) = head {
            return match identifier.first().and_then(SExpr::word) {
                Some("_") => self.parse_indexed_application(identifier, arguments, locals),
                Some("as") => self.parse_qualified_application(identifier, arguments, locals),
                _ => Err(CommandError::message("unsupported qualified identifier")),
            };
        }
        let operator = expect_word(head, "term operator")?;
        if operator == "let" {
            return self.parse_let(arguments, locals);
        }
        if operator == "!" {
            if arguments.is_empty() {
                return Err(CommandError::message("annotation requires a term"));
            }
            return self.parse_term(&arguments[0], locals);
        }
        let terms = arguments
            .iter()
            .map(|argument| self.parse_term(argument, locals))
            .collect::<Result<Vec<_>, _>>()?;
        match operator {
            "not" => {
                expect_term_arity(&terms, 1, "not")?;
                self.terms.not(terms[0]).map_err(CommandError::from)
            }
            "and" => {
                expect_min_term_arity(&terms, 2, "and")?;
                self.terms.and(&terms).map_err(CommandError::from)
            }
            "or" => {
                expect_min_term_arity(&terms, 2, "or")?;
                self.terms.or(&terms).map_err(CommandError::from)
            }
            "xor" => {
                expect_min_term_arity(&terms, 2, "xor")?;
                let mut result = terms[0];
                for &term in &terms[1..] {
                    result = self.terms.xor(result, term).map_err(CommandError::from)?;
                }
                Ok(result)
            }
            "=>" => self.terms.implies(&terms).map_err(CommandError::from),
            "=" => self.terms.equal(&terms).map_err(CommandError::from),
            "distinct" => self.terms.distinct(&terms).map_err(CommandError::from),
            "ite" => {
                expect_term_arity(&terms, 3, "ite")?;
                self.terms
                    .ite(terms[0], terms[1], terms[2])
                    .map_err(CommandError::from)
            }
            "+" => {
                self.require_arithmetic()?;
                self.terms
                    .arithmetic_add(&terms)
                    .map_err(CommandError::from)
            }
            "-" => {
                self.require_arithmetic()?;
                self.terms
                    .arithmetic_sub(&terms)
                    .map_err(CommandError::from)
            }
            "*" => {
                self.require_arithmetic()?;
                self.terms
                    .arithmetic_mul(&terms)
                    .map_err(CommandError::from)
            }
            "/" => {
                self.require_reals()?;
                expect_term_arity(&terms, 2, "/")?;
                self.terms
                    .arithmetic_divide(terms[0], terms[1])
                    .map_err(CommandError::from)
            }
            "<" | "<=" | ">" | ">=" => {
                self.require_arithmetic()?;
                expect_min_term_arity(&terms, 2, operator)?;
                let mut comparisons = Vec::with_capacity(terms.len() - 1);
                for pair in terms.windows(2) {
                    let comparison = match operator {
                        "<" => self.terms.arithmetic_lt(pair[0], pair[1]),
                        "<=" => self.terms.arithmetic_le(pair[0], pair[1]),
                        ">" => self.terms.arithmetic_gt(pair[0], pair[1]),
                        ">=" => self.terms.arithmetic_ge(pair[0], pair[1]),
                        _ => unreachable!("operator covered by outer match"),
                    }
                    .map_err(CommandError::from)?;
                    comparisons.push(comparison);
                }
                self.terms.and(&comparisons).map_err(CommandError::from)
            }
            "select" => {
                self.require_arrays()?;
                expect_term_arity(&terms, 2, "select")?;
                self.terms
                    .select(terms[0], terms[1])
                    .map_err(CommandError::from)
            }
            "store" => {
                self.require_arrays()?;
                expect_term_arity(&terms, 3, "store")?;
                self.terms
                    .store(terms[0], terms[1], terms[2])
                    .map_err(CommandError::from)
            }
            "concat" => {
                self.require_bitvectors()?;
                expect_term_arity(&terms, 2, "concat")?;
                self.terms
                    .concat(terms[0], terms[1])
                    .map_err(CommandError::from)
            }
            "bvnot" => {
                self.require_bitvectors()?;
                expect_term_arity(&terms, 1, "bvnot")?;
                self.terms.bvnot(terms[0]).map_err(CommandError::from)
            }
            "bvneg" => {
                self.require_bitvectors()?;
                expect_term_arity(&terms, 1, "bvneg")?;
                self.terms.bvneg(terms[0]).map_err(CommandError::from)
            }
            "bvand" => {
                self.require_bitvectors()?;
                self.terms.bvand(&terms).map_err(CommandError::from)
            }
            "bvor" => {
                self.require_bitvectors()?;
                self.terms.bvor(&terms).map_err(CommandError::from)
            }
            "bvxor" => {
                self.require_bitvectors()?;
                self.terms.bvxor(&terms).map_err(CommandError::from)
            }
            "bvadd" => {
                self.require_bitvectors()?;
                self.terms.bvadd(&terms).map_err(CommandError::from)
            }
            "bvmul" => {
                self.require_bitvectors()?;
                self.terms.bvmul(&terms).map_err(CommandError::from)
            }
            "bvnand" | "bvnor" | "bvxnor" | "bvcomp" | "bvsub" | "bvudiv" | "bvurem" | "bvsdiv"
            | "bvsrem" | "bvsmod" | "bvshl" | "bvlshr" | "bvashr" | "bvult" | "bvule" | "bvugt"
            | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge" | "bvuaddo" | "bvsaddo"
            | "bvumulo" | "bvsmulo" | "bvusubo" | "bvssubo" | "bvsdivo" => {
                self.require_bitvectors()?;
                expect_term_arity(&terms, 2, operator)?;
                let (left, right) = (terms[0], terms[1]);
                match operator {
                    "bvnand" => self.terms.bvnand(left, right),
                    "bvnor" => self.terms.bvnor(left, right),
                    "bvxnor" => self.terms.bvxnor(left, right),
                    "bvcomp" => self.terms.bvcomp(left, right),
                    "bvsub" => self.terms.bvsub(left, right),
                    "bvudiv" => self.terms.bvudiv(left, right),
                    "bvurem" => self.terms.bvurem(left, right),
                    "bvsdiv" => self.terms.bvsdiv(left, right),
                    "bvsrem" => self.terms.bvsrem(left, right),
                    "bvsmod" => self.terms.bvsmod(left, right),
                    "bvshl" => self.terms.bvshl(left, right),
                    "bvlshr" => self.terms.bvlshr(left, right),
                    "bvashr" => self.terms.bvashr(left, right),
                    "bvult" => self.terms.bvult(left, right),
                    "bvule" => self.terms.bvule(left, right),
                    "bvugt" => self.terms.bvugt(left, right),
                    "bvuge" => self.terms.bvuge(left, right),
                    "bvslt" => self.terms.bvslt(left, right),
                    "bvsle" => self.terms.bvsle(left, right),
                    "bvsgt" => self.terms.bvsgt(left, right),
                    "bvsge" => self.terms.bvsge(left, right),
                    "bvuaddo" => self.terms.bvuaddo(left, right),
                    "bvsaddo" => self.terms.bvsaddo(left, right),
                    "bvumulo" => self.terms.bvumulo(left, right),
                    "bvsmulo" => self.terms.bvsmulo(left, right),
                    "bvusubo" => self.terms.bvusubo(left, right),
                    "bvssubo" => self.terms.bvssubo(left, right),
                    "bvsdivo" => self.terms.bvsdivo(left, right),
                    _ => unreachable!("operator covered by outer match"),
                }
                .map_err(CommandError::from)
            }
            "bvnego" => {
                self.require_bitvectors()?;
                expect_term_arity(&terms, 1, "bvnego")?;
                self.terms.bvnego(terms[0]).map_err(CommandError::from)
            }
            _ => self.apply_function(operator, &terms),
        }
    }

    fn apply_function(&mut self, name: &str, arguments: &[TermId]) -> Result<TermId, CommandError> {
        let binding = self
            .functions
            .get(name)
            .cloned()
            .ok_or_else(|| CommandError::message(format!("unsupported operator `{name}`")))?;
        match binding {
            FunctionBinding::Declared(function) => self
                .terms
                .apply(function, arguments)
                .map_err(CommandError::from),
            FunctionBinding::Defined {
                parameters,
                domain,
                range,
                body,
            } => {
                if arguments.len() != parameters.len() {
                    return Err(CommandError::message(format!(
                        "`{name}` expects {} argument(s), received {}",
                        parameters.len(),
                        arguments.len()
                    )));
                }
                for (&argument, &sort) in arguments.iter().zip(domain.iter()) {
                    if self.terms.sort(argument).map_err(CommandError::from)? != sort {
                        return Err(CommandError::message(format!(
                            "argument to `{name}` does not have its declared sort"
                        )));
                    }
                }
                let locals = parameters
                    .into_iter()
                    .zip(arguments.iter().copied())
                    .collect::<HashMap<_, _>>();
                let result = self.parse_term(&body, &[locals])?;
                if self.terms.sort(result).map_err(CommandError::from)? != range {
                    return Err(CommandError::message(format!(
                        "instantiation of `{name}` has the wrong result sort"
                    )));
                }
                Ok(result)
            }
        }
    }

    fn parse_indexed_constant(&mut self, items: &[SExpr]) -> Result<TermId, CommandError> {
        self.require_bitvectors()?;
        expect_arity(items, 3, "indexed bit-vector constant")?;
        let constructor = expect_symbol(&items[1], "indexed constant name")?;
        let decimal = constructor
            .strip_prefix("bv")
            .filter(|value| !value.is_empty())
            .ok_or_else(|| {
                CommandError::message(format!("unsupported indexed constant `{constructor}`"))
            })?;
        let width = parse_u32(&items[2], "bit-vector width")?;
        self.terms
            .bitvec_from_decimal(decimal, width)
            .map_err(CommandError::from)
    }

    fn parse_qualified_application(
        &mut self,
        identifier: &[SExpr],
        arguments: &[SExpr],
        locals: &[HashMap<String, TermId>],
    ) -> Result<TermId, CommandError> {
        self.require_arrays()?;
        expect_arity(identifier, 3, "qualified array identifier")?;
        if identifier[0].word() != Some("as") || identifier[1].symbol() != Some("const") {
            return Err(CommandError::Unsupported);
        }
        expect_arity(arguments, 1, "constant array")?;
        let Sort::Array(sort) = self.parse_sort(&identifier[2])? else {
            return Err(CommandError::message(
                "qualified `const` must name an array sort",
            ));
        };
        let value = self.parse_term(&arguments[0], locals)?;
        self.terms
            .const_array(sort, value)
            .map_err(CommandError::from)
    }

    fn parse_indexed_application(
        &mut self,
        identifier: &[SExpr],
        arguments: &[SExpr],
        locals: &[HashMap<String, TermId>],
    ) -> Result<TermId, CommandError> {
        self.require_bitvectors()?;
        if identifier.first().and_then(SExpr::word) != Some("_") {
            return Err(CommandError::message(
                "indexed identifier must start with `_`",
            ));
        }
        if identifier.len() < 3 {
            return Err(CommandError::message("incomplete indexed identifier"));
        }
        expect_arity(arguments, 1, "indexed bit-vector operator")?;
        let operator = expect_symbol(&identifier[1], "indexed operator name")?;
        let term = self.parse_term(&arguments[0], locals)?;
        match operator {
            "extract" => {
                expect_arity(&identifier[2..], 2, "extract indices")?;
                let high = parse_u32(&identifier[2], "extract high index")?;
                let low = parse_u32(&identifier[3], "extract low index")?;
                self.terms
                    .extract(term, high, low)
                    .map_err(CommandError::from)
            }
            "repeat" | "zero_extend" | "sign_extend" | "rotate_left" | "rotate_right" => {
                expect_arity(&identifier[2..], 1, operator)?;
                let index = parse_u32(&identifier[2], operator)?;
                match operator {
                    "repeat" => self.terms.repeat(term, index),
                    "zero_extend" => self.terms.zero_extend(term, index),
                    "sign_extend" => self.terms.sign_extend(term, index),
                    "rotate_left" => self.terms.rotate_left(term, index),
                    "rotate_right" => self.terms.rotate_right(term, index),
                    _ => unreachable!("operator covered by outer match"),
                }
                .map_err(CommandError::from)
            }
            _ => Err(CommandError::message(format!(
                "unsupported indexed operator `{operator}`"
            ))),
        }
    }

    fn parse_let(
        &mut self,
        arguments: &[SExpr],
        locals: &[HashMap<String, TermId>],
    ) -> Result<TermId, CommandError> {
        expect_arity(arguments, 2, "let")?;
        let bindings = expect_list(&arguments[0], "let bindings")?;
        let mut scope = HashMap::new();
        for binding in bindings {
            let pair = expect_list(binding, "let binding")?;
            expect_arity(pair, 2, "let binding")?;
            let name = expect_symbol(&pair[0], "let variable")?.to_owned();
            if scope.contains_key(&name) {
                return Err(CommandError::message(format!(
                    "duplicate let variable `{name}`"
                )));
            }
            let value = self.parse_term(&pair[1], locals)?;
            scope.insert(name, value);
        }
        let mut nested = locals.to_vec();
        nested.push(scope);
        self.parse_term(&arguments[1], &nested)
    }

    fn sat_model(&self) -> Result<&Model, CommandError> {
        match &self.last_check {
            LastCheck::Sat { boolean, .. } | LastCheck::Unknown { boolean, .. } => Ok(boolean),
            _ => Err(CommandError::message(
                "model inspection requires a preceding sat or unknown result",
            )),
        }
    }

    fn sat_theory_model(&self) -> Result<&TheoryModel, CommandError> {
        match &self.last_check {
            LastCheck::Sat { theory, .. } | LastCheck::Unknown { theory, .. } => Ok(theory),
            _ => Err(CommandError::message(
                "model inspection requires a preceding sat or unknown result",
            )),
        }
    }

    fn bool_term_value(&self, model: &Model, term: TermId) -> bool {
        self.terms
            .evaluate_bool(term, |symbol| self.symbol_value(model, symbol))
            .expect("asserted and queried terms are Boolean")
    }

    fn render_term_value(
        &self,
        model: &Model,
        theory: &TheoryModel,
        term: TermId,
    ) -> Result<String, CommandError> {
        let value = self.model_value(model, theory, term, &mut HashSet::new())?;
        self.render_model_value(model, theory, value)
    }

    fn render_model_value(
        &self,
        model: &Model,
        theory: &TheoryModel,
        value: ModelValue,
    ) -> Result<String, CommandError> {
        match value {
            ModelValue::Bool(value) => Ok(bool_text(value).to_owned()),
            ModelValue::BitVec(bits) => {
                let digits = bits
                    .into_iter()
                    .rev()
                    .map(|bit| if bit { '1' } else { '0' })
                    .collect::<String>();
                Ok(format!("#b{digits}"))
            }
            ModelValue::Arithmetic(sort, value) => Ok(render_arithmetic_value(sort, &value)),
            ModelValue::Uninterpreted(sort, value) => {
                Ok(self.render_uninterpreted_value(sort, value))
            }
            ModelValue::Array(sort, value) => self.render_array_value(model, theory, sort, value),
        }
    }

    fn model_value(
        &self,
        model: &Model,
        theory: &TheoryModel,
        term: TermId,
        visiting: &mut HashSet<TermId>,
    ) -> Result<ModelValue, CommandError> {
        let application = self.terms.application_for_result(term);
        if application.is_none() {
            return self.direct_model_value(model, theory, term);
        }
        if theory.application_relevant(term) {
            if let Some(value) = self.direct_application_value(model, theory, term)? {
                return Ok(value);
            }
        }
        if !visiting.insert(term) {
            return self.default_model_value(self.terms.sort(term).map_err(CommandError::from)?);
        }
        let application = application.expect("checked above");
        if let Some(sort) = self.terms.select_array_sort(application.function) {
            let source = self.model_value(model, theory, application.arguments[0], visiting)?;
            let ModelValue::Array(source_sort, class) = source else {
                return Err(CommandError::message(
                    "internal select source does not have an array value",
                ));
            };
            debug_assert_eq!(source_sort, sort);
            let value = self.array_value_at(
                model,
                theory,
                sort,
                class,
                application.arguments[1],
                &mut HashSet::new(),
            )?;
            visiting.remove(&term);
            return Ok(value);
        }
        let argument_values = application
            .arguments
            .iter()
            .map(|&argument| self.model_value(model, theory, argument, visiting))
            .collect::<Result<Vec<_>, _>>()?;
        let mut fallback = None;
        for candidate in self.terms.applications().iter().filter(|candidate| {
            theory.application_relevant(candidate.result)
                && candidate.function == application.function
                && candidate.result != term
        }) {
            let Some(value) = self.direct_application_value(model, theory, candidate.result)?
            else {
                continue;
            };
            fallback.get_or_insert_with(|| value.clone());
            let candidate_arguments = candidate
                .arguments
                .iter()
                .map(|&argument| self.model_value(model, theory, argument, visiting))
                .collect::<Result<Vec<_>, _>>()?;
            if candidate_arguments == argument_values {
                visiting.remove(&term);
                return Ok(value);
            }
        }
        visiting.remove(&term);
        if let Some(value) = fallback {
            Ok(value)
        } else {
            self.default_model_value(self.terms.sort(term).map_err(CommandError::from)?)
        }
    }

    fn array_value_at(
        &self,
        model: &Model,
        theory: &TheoryModel,
        sort: ArraySortId,
        class: u32,
        index: TermId,
        visiting: &mut HashSet<(ArraySortId, u32)>,
    ) -> Result<ModelValue, CommandError> {
        let signature = self
            .terms
            .array_signature(sort)
            .map_err(CommandError::from)?;
        let index_value = self.model_value(model, theory, index, &mut HashSet::new())?;
        for application in self.terms.applications().iter().filter(|application| {
            theory.application_relevant(application.result)
                && application.function == signature.select_function
        }) {
            let Some(source_class) = theory.value(application.arguments[0]) else {
                continue;
            };
            if source_class != class
                || self.model_value(model, theory, application.arguments[1], &mut HashSet::new())?
                    != index_value
            {
                continue;
            }
            if let Some(value) = self.direct_application_value(model, theory, application.result)? {
                return Ok(value);
            }
        }
        if !visiting.insert((sort, class)) {
            return self.default_model_value(signature.element);
        }
        for (position, node) in self.terms.nodes.iter().enumerate() {
            let Some(term) = TermId::from_index(position) else {
                continue;
            };
            if self.terms.sort(term).ok() != Some(Sort::Array(sort))
                || theory.value(term) != Some(class)
            {
                continue;
            }
            match node.kind {
                TermKind::ArrayConst(value) => {
                    visiting.remove(&(sort, class));
                    return self.model_value(model, theory, value, &mut HashSet::new());
                }
                TermKind::ArrayStore(base, stored_index, stored_value) => {
                    let stored_index_value =
                        self.model_value(model, theory, stored_index, &mut HashSet::new())?;
                    if stored_index_value == index_value {
                        visiting.remove(&(sort, class));
                        return self.model_value(model, theory, stored_value, &mut HashSet::new());
                    }
                    if let Some(base_class) = theory.value(base) {
                        if base_class != class {
                            let value = self
                                .array_value_at(model, theory, sort, base_class, index, visiting)?;
                            visiting.remove(&(sort, class));
                            return Ok(value);
                        }
                    }
                }
                _ => {}
            }
        }
        visiting.remove(&(sort, class));
        self.default_model_value(signature.element)
    }

    fn array_default_model_value(
        &self,
        model: &Model,
        theory: &TheoryModel,
        sort: ArraySortId,
        class: u32,
        visiting: &mut HashSet<(ArraySortId, u32)>,
    ) -> Result<ModelValue, CommandError> {
        let signature = self
            .terms
            .array_signature(sort)
            .map_err(CommandError::from)?;
        if !visiting.insert((sort, class)) {
            return self.default_model_value(signature.element);
        }
        for (position, node) in self.terms.nodes.iter().enumerate() {
            let Some(term) = TermId::from_index(position) else {
                continue;
            };
            if self.terms.sort(term).ok() != Some(Sort::Array(sort))
                || theory.value(term) != Some(class)
            {
                continue;
            }
            match node.kind {
                TermKind::ArrayConst(value) => {
                    visiting.remove(&(sort, class));
                    return self.model_value(model, theory, value, &mut HashSet::new());
                }
                TermKind::ArrayStore(base, _, _) => {
                    if let Some(base_class) = theory.value(base) {
                        if base_class != class {
                            let value = self.array_default_model_value(
                                model, theory, sort, base_class, visiting,
                            )?;
                            visiting.remove(&(sort, class));
                            return Ok(value);
                        }
                    }
                }
                _ => {}
            }
        }
        visiting.remove(&(sort, class));
        self.default_model_value(signature.element)
    }

    fn direct_application_value(
        &self,
        model: &Model,
        theory: &TheoryModel,
        term: TermId,
    ) -> Result<Option<ModelValue>, CommandError> {
        Ok(match self.terms.sort(term).map_err(CommandError::from)? {
            Sort::Bool => {
                let TermKind::Atom(symbol) = self.terms.node(term).kind else {
                    return Ok(None);
                };
                self.encoder
                    .atom_literal(symbol)
                    .map(|literal| ModelValue::Bool(model.literal_value(literal)))
            }
            Sort::BitVec(_) => {
                let bits = self.terms.bitvec_bits(term).map_err(CommandError::from)?;
                let mut values = Vec::with_capacity(bits.len());
                for &bit in bits {
                    let TermKind::Atom(symbol) = self.terms.node(bit).kind else {
                        return Ok(None);
                    };
                    let Some(literal) = self.encoder.atom_literal(symbol) else {
                        return Ok(None);
                    };
                    values.push(model.literal_value(literal));
                }
                Some(ModelValue::BitVec(values))
            }
            sort @ (Sort::Int | Sort::Real) => Some(ModelValue::Arithmetic(
                sort,
                theory.arithmetic.expression_value(
                    self.terms
                        .arithmetic_expression_for_term(term)
                        .map_err(CommandError::from)?,
                ),
            )),
            Sort::Uninterpreted(sort) => theory
                .value(term)
                .map(|value| ModelValue::Uninterpreted(sort, value)),
            Sort::Array(sort) => theory
                .value(term)
                .map(|value| ModelValue::Array(sort, value)),
        })
    }

    fn direct_model_value(
        &self,
        model: &Model,
        theory: &TheoryModel,
        term: TermId,
    ) -> Result<ModelValue, CommandError> {
        match self.terms.sort(term).map_err(CommandError::from)? {
            Sort::Bool => Ok(ModelValue::Bool(self.bool_term_value(model, term))),
            Sort::BitVec(_) => Ok(ModelValue::BitVec(
                self.terms
                    .evaluate_bitvec(term, |symbol| self.symbol_value(model, symbol))
                    .map_err(CommandError::from)?,
            )),
            sort @ (Sort::Int | Sort::Real) => Ok(ModelValue::Arithmetic(
                sort,
                theory.arithmetic.expression_value(
                    self.terms
                        .arithmetic_expression_for_term(term)
                        .map_err(CommandError::from)?,
                ),
            )),
            Sort::Uninterpreted(sort) => Ok(ModelValue::Uninterpreted(
                sort,
                theory.value(term).unwrap_or(0),
            )),
            Sort::Array(sort) => Ok(ModelValue::Array(sort, theory.value(term).unwrap_or(0))),
        }
    }

    fn default_model_value(&self, sort: Sort) -> Result<ModelValue, CommandError> {
        Ok(match sort {
            Sort::Bool => ModelValue::Bool(false),
            Sort::BitVec(width) => ModelValue::BitVec(vec![false; width as usize]),
            sort @ (Sort::Int | Sort::Real) => ModelValue::Arithmetic(sort, BigRational::zero()),
            Sort::Uninterpreted(sort) => ModelValue::Uninterpreted(sort, 0),
            Sort::Array(sort) => ModelValue::Array(sort, 0),
        })
    }

    fn render_function_model(
        &self,
        model: &Model,
        theory: &TheoryModel,
        declaration: &FunctionDeclaration,
    ) -> Result<String, CommandError> {
        let signature = self
            .terms
            .function_signature(declaration.function)
            .map_err(CommandError::from)?;
        let parameters = signature
            .domain
            .iter()
            .enumerate()
            .map(|(index, &sort)| format!("(x!{index} {})", self.render_sort(sort)))
            .collect::<Vec<_>>();
        let mut seen = HashSet::new();
        let mut rows = Vec::new();
        for application in self.terms.applications().iter().filter(|application| {
            theory.application_relevant(application.result)
                && application.function == declaration.function
        }) {
            let arguments = application
                .arguments
                .iter()
                .map(|&term| self.render_term_value(model, theory, term))
                .collect::<Result<Vec<_>, _>>()?;
            if !seen.insert(arguments.clone()) {
                continue;
            }
            let result = self.render_term_value(model, theory, application.result)?;
            rows.push((arguments, result));
        }
        let mut body = rows
            .first()
            .map(|(_, result)| result.clone())
            .unwrap_or_else(|| self.default_value(signature.range));
        for (arguments, result) in rows.into_iter().rev() {
            let equalities = arguments
                .iter()
                .enumerate()
                .map(|(index, value)| format!("(= x!{index} {value})"))
                .collect::<Vec<_>>();
            let condition = match equalities.as_slice() {
                [single] => single.clone(),
                _ => format!("(and {})", equalities.join(" ")),
            };
            body = format!("(ite {condition} {result} {body})");
        }
        Ok(format!(
            "(define-fun {} ({}) {} {})",
            quote_symbol(&declaration.name),
            parameters.join(" "),
            self.render_sort(signature.range),
            body
        ))
    }

    fn render_array_value(
        &self,
        model: &Model,
        theory: &TheoryModel,
        sort: ArraySortId,
        class: u32,
    ) -> Result<String, CommandError> {
        let signature = self
            .terms
            .array_signature(sort)
            .map_err(CommandError::from)?;
        let default =
            self.array_default_model_value(model, theory, sort, class, &mut HashSet::new())?;
        let default = self.render_model_value(model, theory, default)?;
        let mut array = format!(
            "((as const {}) {default})",
            self.render_sort(Sort::Array(sort))
        );
        let mut seen_indices = HashSet::new();
        for application in self.terms.applications().iter().filter(|application| {
            theory.application_relevant(application.result)
                && application.function == signature.select_function
        }) {
            let Some(&source) = application.arguments.first() else {
                continue;
            };
            if self.model_value(model, theory, source, &mut HashSet::new())?
                != ModelValue::Array(sort, class)
            {
                continue;
            }
            let index = self.render_term_value(model, theory, application.arguments[1])?;
            if !seen_indices.insert(index.clone()) {
                continue;
            }
            let value = self.render_term_value(model, theory, application.result)?;
            if value == default {
                continue;
            }
            array = format!("(store {array} {index} {value})");
        }
        Ok(array)
    }

    fn default_value(&self, sort: Sort) -> String {
        match sort {
            Sort::Bool => "false".to_owned(),
            Sort::BitVec(width) => format!("#b{}", "0".repeat(width as usize)),
            Sort::Int => "0".to_owned(),
            Sort::Real => "0.0".to_owned(),
            Sort::Uninterpreted(sort) => self.render_uninterpreted_value(sort, 0),
            Sort::Array(sort) => {
                let signature = self
                    .terms
                    .array_signature(sort)
                    .expect("model array sort belongs to this term store");
                format!(
                    "((as const {}) {})",
                    self.render_sort(Sort::Array(sort)),
                    self.default_value(signature.element)
                )
            }
        }
    }

    fn render_uninterpreted_value(&self, sort: UninterpretedSortId, value: u32) -> String {
        format!("@uc!{}!{value}", sort.index())
    }

    fn render_sort(&self, sort: Sort) -> String {
        match sort {
            Sort::Bool => "Bool".to_owned(),
            Sort::BitVec(width) => format!("(_ BitVec {width})"),
            Sort::Int => "Int".to_owned(),
            Sort::Real => "Real".to_owned(),
            Sort::Uninterpreted(id) => self
                .sort_names
                .get(&id)
                .map(|name| quote_symbol(name))
                .unwrap_or_else(|| format!("@sort!{}", id.index())),
            Sort::Array(id) => {
                let signature = self
                    .terms
                    .array_signature(id)
                    .expect("rendered array sort belongs to this term store");
                format!(
                    "(Array {} {})",
                    self.render_sort(signature.index),
                    self.render_sort(signature.element)
                )
            }
        }
    }

    fn symbol_value(&self, model: &Model, symbol: SymbolId) -> bool {
        self.encoder
            .atom_literal(symbol)
            .is_some_and(|literal| model.literal_value(literal))
    }

    fn active_declarations(&self) -> impl Iterator<Item = &Declaration> {
        self.frames
            .iter()
            .flat_map(|frame| frame.declarations.iter())
    }

    fn active_function_declarations(&self) -> impl Iterator<Item = &FunctionDeclaration> {
        self.frames
            .iter()
            .flat_map(|frame| frame.function_declarations.iter())
    }

    fn declaration_frame(&self) -> usize {
        if self.options.global_declarations {
            0
        } else {
            self.frames.len() - 1
        }
    }

    fn ensure_fresh_name(&self, name: &str) -> Result<(), CommandError> {
        if name.starts_with(['.', '@']) {
            return Err(CommandError::message(format!(
                "symbol `{name}` uses a solver-reserved prefix"
            )));
        }
        if self.bindings.contains_key(name)
            || self.functions.contains_key(name)
            || is_builtin_symbol(name)
        {
            Err(CommandError::message(format!(
                "symbol `{name}` is already defined"
            )))
        } else {
            Ok(())
        }
    }

    fn ensure_fresh_sort_name(&self, name: &str) -> Result<(), CommandError> {
        if self.sorts.contains_key(name) || matches!(name, "Bool" | "BitVec" | "Int" | "Real") {
            Err(CommandError::message(format!(
                "sort symbol `{name}` is already defined"
            )))
        } else {
            Ok(())
        }
    }

    fn parse_sort(&mut self, expression: &SExpr) -> Result<Sort, CommandError> {
        self.require_logic()?;
        if let Some(symbol) = expression.symbol() {
            if symbol == "Bool" {
                return Ok(Sort::Bool);
            }
            if symbol == "Int" {
                self.require_integers()?;
                return Ok(Sort::Int);
            }
            if symbol == "Real" {
                self.require_reals()?;
                return Ok(Sort::Real);
            }
            return self
                .sorts
                .get(symbol)
                .copied()
                .ok_or_else(|| CommandError::message(format!("unknown sort `{symbol}`")));
        }
        let items = expect_list(expression, "sort")?;
        if items.first().and_then(SExpr::symbol) == Some("Array") {
            self.require_arrays()?;
            expect_arity(items, 3, "array sort")?;
            let index = self.parse_sort(&items[1])?;
            let element = self.parse_sort(&items[2])?;
            if self.options.produce_proofs
                && (matches!(index, Sort::Array(_)) || matches!(element, Sort::Array(_)))
            {
                return Err(CommandError::message(
                    "nested arrays are outside the proof boundary",
                ));
            }
            let sort = self
                .terms
                .array_sort(index, element)
                .map_err(CommandError::from)?;
            return Ok(Sort::Array(sort));
        }
        self.require_bitvectors()?;
        expect_arity(items, 3, "bit-vector sort")?;
        if items[0].word() != Some("_") || items[1].symbol() != Some("BitVec") {
            return Err(CommandError::Unsupported);
        }
        let width = parse_u32(&items[2], "bit-vector width")?;
        if width == 0 {
            return Err(CommandError::message(
                "bit-vector width must be greater than zero",
            ));
        }
        Ok(Sort::BitVec(width))
    }

    fn require_logic(&self) -> Result<(), CommandError> {
        if self.logic.is_some() {
            Ok(())
        } else {
            Err(CommandError::message(
                "set-logic must be issued before declarations or solving",
            ))
        }
    }

    fn require_start_mode(&self, option: &str) -> Result<(), CommandError> {
        if self.logic.is_none() {
            Ok(())
        } else {
            Err(CommandError::message(format!(
                "option `{option}` can only be set before set-logic"
            )))
        }
    }

    fn require_bitvectors(&self) -> Result<(), CommandError> {
        if matches!(
            self.logic.as_deref(),
            Some("ALL" | "QF_BV" | "QF_UFBV" | "QF_ABV" | "QF_AUFBV")
        ) {
            Ok(())
        } else {
            Err(CommandError::Unsupported)
        }
    }

    fn require_uf(&self) -> Result<(), CommandError> {
        if matches!(
            self.logic.as_deref(),
            Some(
                "ALL"
                    | "QF_UF"
                    | "QF_UFBV"
                    | "QF_AUFBV"
                    | "QF_UFIDL"
                    | "QF_UFLIA"
                    | "QF_UFLRA"
                    | "QF_AUFLIA"
            )
        ) {
            Ok(())
        } else {
            Err(CommandError::Unsupported)
        }
    }

    fn require_arrays(&self) -> Result<(), CommandError> {
        if matches!(
            self.logic.as_deref(),
            Some("ALL" | "QF_ABV" | "QF_AUFBV" | "QF_AUFLIA")
        ) {
            Ok(())
        } else {
            Err(CommandError::Unsupported)
        }
    }

    fn require_arithmetic(&self) -> Result<(), CommandError> {
        if matches!(
            self.logic.as_deref(),
            Some(
                "ALL"
                    | "QF_IDL"
                    | "QF_LIA"
                    | "QF_RDL"
                    | "QF_LRA"
                    | "QF_UFIDL"
                    | "QF_UFLIA"
                    | "QF_UFLRA"
                    | "QF_AUFLIA"
            )
        ) {
            Ok(())
        } else {
            Err(CommandError::Unsupported)
        }
    }

    fn require_integers(&self) -> Result<(), CommandError> {
        if matches!(
            self.logic.as_deref(),
            Some("ALL" | "QF_IDL" | "QF_LIA" | "QF_UFIDL" | "QF_UFLIA" | "QF_AUFLIA")
        ) {
            Ok(())
        } else {
            Err(CommandError::Unsupported)
        }
    }

    fn require_reals(&self) -> Result<(), CommandError> {
        if matches!(
            self.logic.as_deref(),
            Some("ALL" | "QF_RDL" | "QF_LRA" | "QF_UFLRA")
        ) {
            Ok(())
        } else {
            Err(CommandError::Unsupported)
        }
    }

    fn active_proof_names(&self) -> Result<ProofNames, CommandError> {
        let mut names = ProofNames::default();
        for declaration in self.active_declarations() {
            match &self.terms.node(declaration.term).kind {
                TermKind::Atom(symbol) => {
                    names.insert_bool(*symbol, declaration.name.clone());
                }
                TermKind::BitVec(bits) => {
                    for (index, &bit) in bits.iter().enumerate() {
                        let TermKind::Atom(symbol) = self.terms.node(bit).kind else {
                            return Err(CommandError::message(format!(
                                "proof declaration `{}` has a non-atomic bit",
                                declaration.name
                            )));
                        };
                        let index = u32::try_from(index).map_err(|_| {
                            CommandError::message(format!(
                                "proof declaration `{}` is too wide",
                                declaration.name
                            ))
                        })?;
                        names.insert_bit(symbol, declaration.name.clone(), index);
                    }
                }
                TermKind::UfConstant(_) => {
                    names.insert_constant(declaration.term, declaration.name.clone());
                }
                TermKind::Arithmetic(_) => {
                    let variable = self
                        .terms
                        .arithmetic_variable_for_term(declaration.term)
                        .map_err(CommandError::from)?
                        .ok_or_else(|| {
                            CommandError::message(format!(
                                "proof declaration `{}` is not a canonical arithmetic variable",
                                declaration.name
                            ))
                        })?;
                    let sort = self
                        .terms
                        .sort(declaration.term)
                        .map_err(CommandError::from)?;
                    names
                        .insert_arithmetic(variable, sort, declaration.name.clone())
                        .map_err(CommandError::from)?;
                }
                _ => {
                    return Err(CommandError::message(format!(
                        "proof declaration `{}` has an unsupported sort",
                        declaration.name
                    )));
                }
            }
        }
        for declaration in self.active_function_declarations() {
            names.insert_function(declaration.function, declaration.name.clone());
        }
        for (&sort, name) in &self.sort_names {
            names.insert_sort(sort, name.clone());
        }
        Ok(names)
    }

    fn invalidate_check(&mut self) {
        self.last_check = LastCheck::None;
    }
}

/// Result of one SMT-LIB command.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommandOutput {
    pub response: Option<String>,
    pub exit: bool,
}

impl CommandOutput {
    fn silent() -> Self {
        Self {
            response: None,
            exit: false,
        }
    }

    fn text(text: impl Into<String>) -> Self {
        Self {
            response: Some(text.into()),
            exit: false,
        }
    }

    fn error(message: &str) -> Self {
        Self::text(format!("(error {})", quote_string(message)))
    }
}

enum CommandValue {
    Success,
    Text(String),
    Exit,
}

enum CommandError {
    Unsupported,
    Message(String),
}

impl CommandError {
    fn message(message: impl Into<String>) -> Self {
        Self::Message(message.into())
    }
}

impl<E: Error> From<E> for CommandError {
    fn from(error: E) -> Self {
        Self::Message(error.to_string())
    }
}

/// Runs an online SMT-LIB session, emitting and flushing each response before
/// reading the next top-level command.
pub fn run<R: BufRead, W: Write>(input: R, mut output: W) -> Result<(), SessionIoError> {
    let mut reader = Reader::new(input);
    let mut session = Session::new();
    let mut channels = OutputChannels::new(&mut output);
    loop {
        let command = match reader.next() {
            Ok(Some(command)) => command,
            Ok(None) => return Ok(()),
            Err(error) if error.is_recoverable() => {
                let response = CommandOutput::error(&error.to_string());
                channels.write_regular(
                    session.regular_output_channel(),
                    response.response.as_deref().expect("errors have responses"),
                )?;
                continue;
            }
            Err(error) => return Err(SessionIoError::parse(error)),
        };
        let previous_regular = session.regular_output_channel().to_owned();
        let previous_diagnostic = session.diagnostic_output_channel().to_owned();
        let result = session.execute(&command);
        let requested_regular = session.regular_output_channel().to_owned();
        let requested_diagnostic = session.diagnostic_output_channel().to_owned();
        if let Err(error) = channels.prepare_regular(&requested_regular) {
            session.restore_regular_output_channel(previous_regular.clone());
            let response = CommandOutput::error(&format!(
                "could not open regular output channel `{requested_regular}`: {error}"
            ));
            channels.write_regular(
                &previous_regular,
                response.response.as_deref().expect("errors have responses"),
            )?;
            continue;
        }
        if let Err(error) = channels.prepare_diagnostic(&requested_diagnostic) {
            session.restore_diagnostic_output_channel(previous_diagnostic);
            let response = CommandOutput::error(&format!(
                "could not open diagnostic output channel `{requested_diagnostic}`: {error}"
            ));
            channels.write_regular(
                &requested_regular,
                response.response.as_deref().expect("errors have responses"),
            )?;
            continue;
        }
        if let Some(response) = result.response {
            channels.write_regular(&requested_regular, &response)?;
        }
        if result.exit {
            return Ok(());
        }
    }
}

struct OutputChannels<'a, W> {
    stdout: &'a mut W,
    regular_file: Option<(String, File)>,
    diagnostic_file: Option<(String, File)>,
}

impl<'a, W: Write> OutputChannels<'a, W> {
    fn new(stdout: &'a mut W) -> Self {
        Self {
            stdout,
            regular_file: None,
            diagnostic_file: None,
        }
    }

    fn prepare_regular(&mut self, channel: &str) -> std::io::Result<()> {
        if channel == "stdout" {
            self.regular_file = None;
            return Ok(());
        }
        if self
            .regular_file
            .as_ref()
            .is_some_and(|(current, _)| current == channel)
        {
            return Ok(());
        }
        let file = open_output_channel(channel)?;
        self.regular_file = Some((channel.to_owned(), file));
        Ok(())
    }

    fn prepare_diagnostic(&mut self, channel: &str) -> std::io::Result<()> {
        if channel == "stderr" {
            self.diagnostic_file = None;
            return Ok(());
        }
        if self
            .diagnostic_file
            .as_ref()
            .is_some_and(|(current, _)| current == channel)
        {
            return Ok(());
        }
        let file = open_output_channel(channel)?;
        self.diagnostic_file = Some((channel.to_owned(), file));
        Ok(())
    }

    fn write_regular(&mut self, channel: &str, response: &str) -> Result<(), SessionIoError> {
        let output: &mut dyn Write = if channel == "stdout" {
            self.stdout
        } else {
            let Some((current, file)) = &mut self.regular_file else {
                return Err(SessionIoError::io(std::io::Error::other(format!(
                    "regular output channel `{channel}` is not open"
                ))));
            };
            if current != channel {
                return Err(SessionIoError::io(std::io::Error::other(format!(
                    "regular output channel `{channel}` is not active"
                ))));
            }
            file
        };
        writeln!(output, "{response}").map_err(SessionIoError::io)?;
        output.flush().map_err(SessionIoError::io)
    }
}

fn open_output_channel(channel: &str) -> std::io::Result<File> {
    OpenOptions::new().create(true).append(true).open(channel)
}

#[derive(Debug)]
pub struct SessionIoError(String);

impl SessionIoError {
    fn parse(error: impl Error) -> Self {
        Self(error.to_string())
    }

    fn io(error: impl Error) -> Self {
        Self(format!("SMT-LIB output error: {error}"))
    }
}

impl fmt::Display for SessionIoError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl Error for SessionIoError {}

fn expect_list<'a>(expression: &'a SExpr, role: &str) -> Result<&'a [SExpr], CommandError> {
    let SExpr::List(items) = expression else {
        return Err(CommandError::message(format!("{role} must be a list")));
    };
    Ok(items)
}

fn expect_symbol<'a>(expression: &'a SExpr, role: &str) -> Result<&'a str, CommandError> {
    expression
        .symbol()
        .ok_or_else(|| CommandError::message(format!("{role} must be a symbol")))
}

fn expect_word<'a>(expression: &'a SExpr, role: &str) -> Result<&'a str, CommandError> {
    expression
        .word()
        .ok_or_else(|| CommandError::message(format!("{role} must be a symbol or reserved word")))
}

fn expect_keyword<'a>(expression: &'a SExpr, role: &str) -> Result<&'a str, CommandError> {
    expression
        .keyword()
        .ok_or_else(|| CommandError::message(format!("{role} must be a keyword")))
}

fn expect_string<'a>(expression: &'a SExpr, role: &str) -> Result<&'a str, CommandError> {
    expression
        .string()
        .ok_or_else(|| CommandError::message(format!("{role} must be a string literal")))
}

fn expect_arity(items: &[SExpr], expected: usize, name: &str) -> Result<(), CommandError> {
    if items.len() == expected {
        Ok(())
    } else {
        Err(CommandError::message(format!(
            "`{name}` expects {expected} argument(s), received {}",
            items.len()
        )))
    }
}

fn expect_term_arity(items: &[TermId], expected: usize, name: &str) -> Result<(), CommandError> {
    if items.len() == expected {
        Ok(())
    } else {
        Err(CommandError::message(format!(
            "`{name}` expects {expected} argument(s), received {}",
            items.len()
        )))
    }
}

fn expect_min_term_arity(items: &[TermId], minimum: usize, name: &str) -> Result<(), CommandError> {
    if items.len() >= minimum {
        Ok(())
    } else {
        Err(CommandError::message(format!(
            "`{name}` expects at least {minimum} arguments, received {}",
            items.len()
        )))
    }
}

fn expect_bool_atom(expression: &SExpr, role: &str) -> Result<bool, CommandError> {
    match expression.symbol() {
        Some("true") => Ok(true),
        Some("false") => Ok(false),
        _ => Err(CommandError::message(format!(
            "{role} expects `true` or `false`"
        ))),
    }
}

fn parse_usize(expression: &SExpr, role: &str) -> Result<usize, CommandError> {
    let numeral = expression
        .numeral()
        .ok_or_else(|| CommandError::message(format!("{role} must be a numeral")))?;
    numeral
        .parse()
        .map_err(|_| CommandError::message(format!("{role} is too large")))
}

fn parse_u32(expression: &SExpr, role: &str) -> Result<u32, CommandError> {
    let numeral = expression
        .numeral()
        .ok_or_else(|| CommandError::message(format!("{role} must be a numeral")))?;
    numeral
        .parse()
        .map_err(|_| CommandError::message(format!("{role} is too large")))
}

type InlineTermContext<'a> = (&'a SExpr, Vec<HashSet<String>>);

fn strip_inline_definitions(
    command: &SExpr,
) -> Result<(SExpr, Vec<InlineDefinitionSyntax>, Option<String>), CommandError> {
    let SExpr::List(items) = command else {
        return Ok((command.clone(), Vec::new(), None));
    };
    let Some((head, arguments)) = items.split_first() else {
        return Ok((command.clone(), Vec::new(), None));
    };
    let Some(name) = head.word() else {
        return Ok((command.clone(), Vec::new(), None));
    };
    let contexts = inline_term_contexts(name, arguments)?;
    if contexts.is_empty() {
        return Ok((command.clone(), Vec::new(), None));
    }

    let mut ordered_names = Vec::new();
    for (expression, _) in &contexts {
        collect_inline_label_names(expression, &mut ordered_names)?;
    }
    let mut all_names = HashSet::new();
    for label in &ordered_names {
        if !all_names.insert(label.clone()) {
            return Err(CommandError::message(format!(
                "inline label `{label}` is repeated in the command"
            )));
        }
    }

    let assertion_label = if name == "assert" && arguments.len() == 1 {
        annotation_name(&arguments[0])?
    } else {
        None
    };
    let mut available = HashSet::new();
    let mut definitions = Vec::with_capacity(ordered_names.len());
    let mut stripped_terms = Vec::with_capacity(contexts.len());
    for (expression, locals) in contexts {
        stripped_terms.push(strip_inline_term(
            expression,
            &all_names,
            &mut available,
            &locals,
            &mut definitions,
        )?);
    }

    let mut stripped = items.clone();
    match name {
        "assert" if arguments.len() == 1 => stripped[1] = stripped_terms.remove(0),
        "define-const" if arguments.len() == 3 => stripped[3] = stripped_terms.remove(0),
        "define-fun" if arguments.len() == 4 => stripped[4] = stripped_terms.remove(0),
        "check-sat-assuming" | "get-value" if arguments.len() == 1 => {
            stripped[1] = SExpr::List(stripped_terms);
        }
        _ => {}
    }
    Ok((SExpr::List(stripped), definitions, assertion_label))
}

fn inline_term_contexts<'a>(
    command: &str,
    arguments: &'a [SExpr],
) -> Result<Vec<InlineTermContext<'a>>, CommandError> {
    let empty = Vec::new();
    match command {
        "assert" if arguments.len() == 1 => Ok(vec![(&arguments[0], empty)]),
        "define-const" if arguments.len() == 3 => Ok(vec![(&arguments[2], empty)]),
        "define-fun" if arguments.len() == 4 => {
            let parameters = expect_list(&arguments[1], "function parameters")?;
            let mut names = HashSet::new();
            for parameter in parameters {
                let fields = expect_list(parameter, "function parameter")?;
                expect_arity(fields, 2, "function parameter")?;
                names.insert(expect_symbol(&fields[0], "parameter name")?.to_owned());
            }
            Ok(vec![(&arguments[3], vec![names])])
        }
        "check-sat-assuming" if arguments.len() == 1 => {
            Ok(expect_list(&arguments[0], "assumption list")?
                .iter()
                .map(|expression| (expression, Vec::new()))
                .collect())
        }
        "get-value" if arguments.len() == 1 => {
            Ok(expect_list(&arguments[0], "get-value term list")?
                .iter()
                .map(|expression| (expression, Vec::new()))
                .collect())
        }
        _ => Ok(Vec::new()),
    }
}

fn collect_inline_label_names(
    expression: &SExpr,
    names: &mut Vec<String>,
) -> Result<(), CommandError> {
    let SExpr::List(items) = expression else {
        return Ok(());
    };
    let Some((head, arguments)) = items.split_first() else {
        return Ok(());
    };
    if head.word() == Some("!") {
        if arguments.is_empty() {
            return Err(CommandError::message("annotation requires a term"));
        }
        collect_inline_label_names(&arguments[0], names)?;
        if let Some(name) = annotation_name(expression)? {
            names.push(name);
        }
        return Ok(());
    }
    if head.word() == Some("let") {
        expect_arity(arguments, 2, "let")?;
        for binding in expect_list(&arguments[0], "let bindings")? {
            let pair = expect_list(binding, "let binding")?;
            expect_arity(pair, 2, "let binding")?;
            collect_inline_label_names(&pair[1], names)?;
        }
        collect_inline_label_names(&arguments[1], names)?;
        return Ok(());
    }
    for argument in arguments {
        collect_inline_label_names(argument, names)?;
    }
    Ok(())
}

fn strip_inline_term(
    expression: &SExpr,
    all_names: &HashSet<String>,
    available: &mut HashSet<String>,
    locals: &[HashSet<String>],
    definitions: &mut Vec<InlineDefinitionSyntax>,
) -> Result<SExpr, CommandError> {
    if let Some(symbol) = expression.symbol() {
        let local = locals.iter().rev().any(|scope| scope.contains(symbol));
        if all_names.contains(symbol) && !available.contains(symbol) && !local {
            return Err(CommandError::message(format!(
                "inline label `{symbol}` is used before its definition"
            )));
        }
        return Ok(expression.clone());
    }
    let SExpr::List(items) = expression else {
        return Ok(expression.clone());
    };
    let Some((head, arguments)) = items.split_first() else {
        return Ok(expression.clone());
    };
    if head.word() == Some("!") {
        if arguments.is_empty() {
            return Err(CommandError::message("annotation requires a term"));
        }
        let term = strip_inline_term(&arguments[0], all_names, available, locals, definitions)?;
        if let Some(name) = annotation_name(expression)? {
            definitions.push(InlineDefinitionSyntax {
                name: name.clone(),
                expression: term.clone(),
            });
            available.insert(name);
        }
        return Ok(term);
    }
    if head.word() == Some("let") {
        expect_arity(arguments, 2, "let")?;
        let bindings = expect_list(&arguments[0], "let bindings")?;
        let mut stripped_bindings = Vec::with_capacity(bindings.len());
        let mut names = HashSet::new();
        for binding in bindings {
            let pair = expect_list(binding, "let binding")?;
            expect_arity(pair, 2, "let binding")?;
            let name = expect_symbol(&pair[0], "let variable")?.to_owned();
            let value = strip_inline_term(&pair[1], all_names, available, locals, definitions)?;
            names.insert(name);
            stripped_bindings.push(SExpr::List(vec![pair[0].clone(), value]));
        }
        let mut nested = locals.to_vec();
        nested.push(names);
        let body = strip_inline_term(&arguments[1], all_names, available, &nested, definitions)?;
        return Ok(SExpr::List(vec![
            head.clone(),
            SExpr::List(stripped_bindings),
            body,
        ]));
    }

    let mut stripped = Vec::with_capacity(items.len());
    stripped.push(head.clone());
    for argument in arguments {
        stripped.push(strip_inline_term(
            argument,
            all_names,
            available,
            locals,
            definitions,
        )?);
    }
    Ok(SExpr::List(stripped))
}

fn annotation_name(expression: &SExpr) -> Result<Option<String>, CommandError> {
    let SExpr::List(items) = expression else {
        return Ok(None);
    };
    if items.first().and_then(SExpr::word) != Some("!") {
        return Ok(None);
    }
    if items.len() < 2 {
        return Err(CommandError::message("annotation requires a term"));
    }
    if items.len() == 2 {
        return Err(CommandError::message(
            "annotation requires at least one attribute",
        ));
    }

    let mut name = None;
    let mut index = 2;
    while index < items.len() {
        let keyword = expect_keyword(&items[index], "annotation attribute")?;
        index += 1;
        match keyword {
            ":named" => {
                if name.is_some() {
                    return Err(CommandError::message(
                        "annotation contains more than one :named attribute",
                    ));
                }
                let Some(value) = items.get(index) else {
                    return Err(CommandError::message(
                        "annotation attribute `:named` has no value",
                    ));
                };
                name = Some(expect_symbol(value, "inline label")?.to_owned());
                index += 1;
            }
            ":pattern" => {
                let Some(value) = items.get(index) else {
                    return Err(CommandError::message(
                        "annotation attribute `:pattern` has no value",
                    ));
                };
                expect_list(value, "annotation pattern")?;
                index += 1;
            }
            _ => {
                if items
                    .get(index)
                    .is_some_and(|value| value.keyword().is_none())
                {
                    index += 1;
                }
            }
        }
    }
    Ok(name)
}

fn render_arithmetic_value(sort: Sort, value: &BigRational) -> String {
    debug_assert!(matches!(sort, Sort::Int | Sort::Real));
    debug_assert!(sort != Sort::Int || value.is_integer());
    let negative = value.is_negative();
    let absolute = value.abs();
    let numerator = absolute.numer();
    let denominator = absolute.denom();
    let body = match sort {
        Sort::Int => numerator.to_string(),
        Sort::Real if denominator == &BigInt::from(1) => format!("{numerator}.0"),
        Sort::Real => format!("(/ {numerator}.0 {denominator}.0)"),
        _ => unreachable!("caller checks the arithmetic sort"),
    };
    if negative {
        format!("(- {body})")
    } else {
        body
    }
}

fn bool_text(value: bool) -> &'static str {
    if value { "true" } else { "false" }
}

fn is_builtin_symbol(symbol: &str) -> bool {
    matches!(
        symbol,
        "Bool"
            | "true"
            | "false"
            | "not"
            | "=>"
            | "and"
            | "or"
            | "xor"
            | "="
            | "distinct"
            | "ite"
            | "BitVec"
            | "Array"
            | "select"
            | "store"
            | "const"
            | "concat"
            | "extract"
            | "repeat"
            | "zero_extend"
            | "sign_extend"
            | "rotate_left"
            | "rotate_right"
            | "bvnot"
            | "bvneg"
            | "bvand"
            | "bvor"
            | "bvxor"
            | "bvnand"
            | "bvnor"
            | "bvxnor"
            | "bvcomp"
            | "bvadd"
            | "bvsub"
            | "bvmul"
            | "bvudiv"
            | "bvurem"
            | "bvsdiv"
            | "bvsrem"
            | "bvsmod"
            | "bvshl"
            | "bvlshr"
            | "bvashr"
            | "bvult"
            | "bvule"
            | "bvugt"
            | "bvuge"
            | "bvslt"
            | "bvsle"
            | "bvsgt"
            | "bvsge"
            | "bvnego"
            | "bvuaddo"
            | "bvsaddo"
            | "bvumulo"
            | "bvsmulo"
            | "bvusubo"
            | "bvssubo"
            | "bvsdivo"
    )
}

fn render(expression: &SExpr) -> String {
    match expression {
        SExpr::Atom(atom) => match atom.kind {
            super::sexpr::AtomKind::String => quote_string(&atom.text),
            super::sexpr::AtomKind::Symbol => quote_symbol(&atom.text),
            _ => atom.text.clone(),
        },
        SExpr::List(items) => {
            let contents = items.iter().map(render).collect::<Vec<_>>().join(" ");
            format!("({contents})")
        }
    }
}

fn quote_string(text: &str) -> String {
    format!("\"{}\"", text.replace('"', "\"\""))
}

fn quote_symbol(symbol: &str) -> String {
    let simple = !symbol.is_empty()
        && !super::sexpr::is_reserved_word(symbol)
        && !symbol
            .bytes()
            .next()
            .is_some_and(|byte| byte.is_ascii_digit())
        && symbol.bytes().all(|byte| {
            byte.is_ascii_alphanumeric()
                || matches!(
                    byte,
                    b'~' | b'!'
                        | b'@'
                        | b'$'
                        | b'%'
                        | b'^'
                        | b'&'
                        | b'*'
                        | b'_'
                        | b'-'
                        | b'+'
                        | b'='
                        | b'<'
                        | b'>'
                        | b'.'
                        | b'?'
                        | b'/'
                )
        });
    if simple {
        symbol.to_owned()
    } else {
        format!("|{symbol}|")
    }
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::io::{BufReader, Cursor};
    use std::path::PathBuf;
    use std::sync::atomic::{AtomicUsize, Ordering};

    use super::run;

    static NEXT_OUTPUT_FILE: AtomicUsize = AtomicUsize::new(0);

    fn execute(script: &str) -> String {
        let mut output = Vec::new();
        run(BufReader::new(Cursor::new(script.as_bytes())), &mut output).unwrap();
        String::from_utf8(output).unwrap()
    }

    fn output_test_path(label: &str) -> PathBuf {
        let sequence = NEXT_OUTPUT_FILE.fetch_add(1, Ordering::Relaxed);
        std::env::temp_dir().join(format!(
            "satrap-smt-session-{label}-{}-{sequence}.log",
            std::process::id()
        ))
    }

    #[test]
    fn online_boolean_session_supports_models_and_scopes() {
        let output = execute(
            "(set-option :print-success true)
             (set-option :produce-models true)
             (set-logic QF_BOOL)
             (declare-const p Bool)
             (declare-const q Bool)
             (assert (or p q))
             (check-sat)
             (get-model)
             (push 1)
             (assert (not p))
             (assert (not q))
             (check-sat)
             (pop 1)
             (check-sat)
             (exit)",
        );
        assert!(output.contains("success\nsat\n(\n  (define-fun"));
        assert!(output.contains("(define-fun p () Bool"));
        assert!(output.contains("\nunsat\nsuccess\nsat\n"));
    }

    #[test]
    fn named_cores_and_arbitrary_assumptions_are_reported_separately() {
        let output = execute(
            "(set-option :produce-unsat-cores true)
             (set-option :produce-unsat-assumptions true)
             (set-logic QF_BOOL)
             (declare-const p Bool)
             (declare-const q Bool)
             (assert (! (=> p q) :named implication))
             (assert (! p :named premise))
             (check-sat-assuming ((not q)))
             (get-unsat-core)
             (get-unsat-assumptions)",
        );
        assert_eq!(output, "unsat\n(implication premise)\n((not q))\n");
    }

    #[test]
    fn qf_bool_proofs_replay_active_scopes_as_permanent_formulas() {
        let output = execute(
            "(set-option :produce-proofs true)
             (get-option :produce-proofs)
             (set-logic QF_BOOL)
             (declare-const p Bool)
             (push 1)
             (assert (! p :named premise))
             (assert (not p))
             (check-sat)
             (get-proof)",
        );
        assert!(output.starts_with("true\nunsat\n(satrap-edrat :version 1 :logic QF_BOOL"));
        assert!(output.contains(":premises (\"(! p :named premise)\" \"(not p)\")"));
        assert!(output.contains("(formula 1)"));
        assert!(output.contains("(formula -1)"));
        assert!(output.ends_with("0\n\")\n"));
    }

    #[test]
    fn get_proof_rejects_nonempty_check_sat_assumptions() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_BOOL)
             (declare-const p Bool)
             (assert p)
             (check-sat-assuming ((not p)))
             (get-proof)",
        );
        assert_eq!(
            output,
            "unsat\n\
             (error \"get-proof requires the preceding check to have an empty assumption set\")\n"
        );
    }

    #[test]
    fn get_proof_accepts_an_empty_check_sat_assumption_list() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_BOOL)
             (assert false)
             (check-sat-assuming ())
             (get-proof)",
        );
        assert!(output.starts_with("unsat\n(satrap-edrat :version 1 :logic QF_BOOL"));
        assert!(output.contains(":premises (\"false\")"));
        assert!(output.ends_with("0\n\")\n"));
    }

    #[test]
    fn proof_inspection_is_invalidated_by_context_mutation() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_BOOL)
             (assert false)
             (check-sat)
             (push 1)
             (get-proof)",
        );
        assert_eq!(
            output,
            "unsat\n\
             (error \"get-proof requires a preceding unsat result\")\n"
        );
    }

    #[test]
    fn proof_mode_rejects_unimplemented_logics_without_mutating_the_session() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_NIA)
             (set-logic QF_BOOL)
             (check-sat)
             (get-proof)",
        );
        assert_eq!(
            output,
            "unsupported\nsat\n\
             (error \"get-proof requires a preceding unsat result\")\n"
        );
    }

    #[test]
    fn proof_mode_rejects_nested_array_sorts_at_the_declaration_boundary() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_ABV)
             (declare-const nested
               (Array (_ BitVec 1) (Array (_ BitVec 1) (_ BitVec 1))))",
        );
        assert_eq!(
            output,
            "(error \"nested arrays are outside the proof boundary\")\n"
        );
    }

    #[test]
    fn qf_uf_proofs_include_canonical_congruence_axioms() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_UF)
             (declare-sort U 0)
             (declare-const a U)
             (declare-const b U)
             (declare-fun f (U) U)
             (assert (= a b))
             (assert (distinct (f a) (f b)))
             (check-sat)
             (get-proof)",
        );
        assert!(output.starts_with("unsat\n(satrap-edrat :version 1 :logic QF_UF"));
        assert!(output.contains(":premises (\"(= a b)\" \"(distinct (f a) (f b))\")"));
        assert!(output.contains("(theory "));
        assert!(output.ends_with("0\n\")\n"));
    }

    #[test]
    fn qf_uf_proofs_ignore_unrelated_internal_allocation_history() {
        let query = "
             (declare-sort U 0)
             (declare-const a U)
             (declare-const b U)
             (declare-fun f (U) U)
             (assert (= a b))
             (assert (distinct (f a) (f b)))
             (check-sat)
             (get-proof)";
        let baseline = execute(&format!(
            "(set-option :produce-proofs true)
             (set-logic QF_UF)
             {query}"
        ));
        let shifted = execute(&format!(
            "(set-option :produce-proofs true)
             (set-logic QF_UF)
             (declare-sort Unused 0)
             (declare-const unused Unused)
             (declare-fun unused-function (Unused) Unused)
             {query}"
        ));
        assert_eq!(baseline, shifted);
    }

    #[test]
    fn qf_ufbv_proofs_combine_congruence_with_named_bits() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_UFBV)
             (declare-sort U 0)
             (declare-const a U)
             (declare-const b U)
             (declare-const x (_ BitVec 2))
             (declare-const y (_ BitVec 2))
             (declare-fun f (U (_ BitVec 2)) (_ BitVec 2))
             (assert (= a b))
             (assert (= x y))
             (assert (distinct (f a x) (f b y)))
             (check-sat)
             (get-proof)",
        );
        assert!(output.starts_with("unsat\n(satrap-edrat :version 1 :logic QF_UFBV"));
        assert!(output.contains("(theory "));
        assert!(output.ends_with("0\n\")\n"));
    }

    #[test]
    fn qf_bv_proofs_use_named_declaration_bits() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_BV)
             (declare-const x (_ BitVec 2))
             (assert (= x #b00))
             (assert (= (bvadd x #b01) #b00))
             (check-sat)
             (get-proof)",
        );
        assert!(output.starts_with("unsat\n(satrap-edrat :version 1 :logic QF_BV"));
        assert!(output.contains(":premises (\"(= x #b00)\" \"(= (bvadd x #b01) #b00)\")"));
        assert!(output.ends_with("0\n\")\n"));
    }

    #[test]
    fn stale_model_queries_are_rejected_after_mutation() {
        let output = execute(
            "(set-option :produce-models true)
             (set-logic QF_BOOL)
             (declare-const p Bool)
             (check-sat)
             (assert p)
             (get-model)",
        );
        assert!(output.ends_with(
            "(error \"model inspection requires a preceding sat or unknown result\")\n"
        ));
    }

    #[test]
    fn qf_bv_session_reconstructs_values_and_uses_standard_model_shape() {
        let output = execute(
            "(set-option :produce-models true)
             (set-logic QF_BV)
             (declare-const x (_ BitVec 4))
             (declare-const y (_ BitVec 4))
             (assert (= (bvadd x #b0011) (_ bv5 4)))
             (assert (= y (bvmul x #x2)))
             (check-sat)
             (get-value (x y (concat x y) ((_ extract 2 1) y)))
             (get-model)",
        );
        assert_eq!(
            output,
            "sat\n\
             ((x #b0010) (y #b0100) ((concat x y) #b00100100) \
             (((_ extract 2 1) y) #b10))\n\
             (\n  (define-fun x () (_ BitVec 4) #b0010)\n  \
             (define-fun y () (_ BitVec 4) #b0100)\n)\n"
        );
    }

    #[test]
    fn resource_unknown_has_a_protocol_model_and_remains_reusable() {
        let output = execute(
            "(set-option :produce-models true)
             (set-option :produce-assignments true)
             (set-logic QF_BOOL)
             (set-option :reproducible-resource-limit 1)
             (declare-const p Bool)
             (declare-const q Bool)
             (assert (! (or p q) :named c1))
             (assert (! (or p (not q)) :named c2))
             (assert (! (or (not p) q) :named c3))
             (assert (! (or (not p) (not q)) :named c4))
             (check-sat)
             (get-info :reason-unknown)
             (get-value (p q (xor p q)))
             (get-assignment)
             (get-model)
             (set-option :reproducible-resource-limit 0)
             (check-sat)",
        );
        assert_eq!(
            output,
            "unknown\n(:reason-unknown resourceout)\n\
             ((p false) (q false) ((xor p q) false))\n\
             ((c1 false) (c2 true) (c3 true) (c4 true))\n\
             (\n  (define-fun p () Bool false)\n  \
             (define-fun q () Bool false)\n)\n\
             unsat\n"
        );
    }

    #[test]
    fn assignment_labels_follow_their_definition_scope() {
        let scoped = execute(
            "(set-option :produce-assignments true)
             (set-logic QF_BOOL)
             (declare-const p Bool)
             (push 1)
             (assert (! p :named scoped))
             (check-sat)
             (get-assignment)
             (pop 1)
             (check-sat)
             (get-assignment)
             (assert scoped)
             (check-sat)",
        );
        assert_eq!(
            scoped,
            "sat\n((scoped true))\nsat\n()\n\
             (error \"unknown symbol `scoped`\")\nsat\n"
        );

        let global = execute(
            "(set-option :produce-assignments true)
             (set-option :global-declarations true)
             (set-logic QF_BOOL)
             (declare-const p Bool)
             (push 1)
             (assert (! p :named global_label))
             (check-sat)
             (get-assignment)
             (pop 1)
             (check-sat)
             (get-assignment)
             (assert (= global_label p))
             (check-sat)",
        );
        let lines = global.lines().collect::<Vec<_>>();
        assert_eq!(lines[0], "sat");
        assert_eq!(lines[1], "((global_label true))");
        assert_eq!(lines[2], "sat");
        assert!(
            matches!(lines[3], "((global_label true))" | "((global_label false))"),
            "unexpected global label assignment:\n{global}"
        );
        assert_eq!(lines[4], "sat");
    }

    #[test]
    fn inline_definitions_follow_postorder_and_feed_assignment_queries() {
        let output = execute(
            "(set-option :produce-models true)
             (set-option :produce-assignments true)
             (set-option :produce-assertions true)
             (set-logic QF_BV)
             (declare-const p Bool)
             (assert (and (! p :named first) (= first p)))
             (assert (= (! #x2a :named answer) answer))
             (check-sat)
             (get-assignment)
             (get-value (answer))
             (get-assertions)",
        );
        assert_eq!(
            output,
            "sat\n((first true))\n((answer #b00101010))\n\
             ((and (! p :named first) (= first p)) \
             (= (! #x2a :named answer) answer))\n"
        );
    }

    #[test]
    fn only_the_outer_assertion_label_participates_in_the_unsat_core() {
        let output = execute(
            "(set-option :produce-assignments true)
             (set-option :produce-unsat-cores true)
             (set-logic QF_BOOL)
             (declare-const p Bool)
             (declare-const q Bool)
             (assert (! (or (! p :named inner) q) :named outer))
             (check-sat)
             (get-assignment)
             (assert (not p))
             (assert (not q))
             (check-sat)
             (get-unsat-core)",
        );
        let mut lines = output.lines();
        assert_eq!(lines.next(), Some("sat"));
        let assignments = lines.next().expect("assignment response");
        assert!(assignments.starts_with("((inner "));
        assert!(assignments.contains(") (outer true))"));
        assert_eq!(lines.next(), Some("unsat"));
        assert_eq!(lines.next(), Some("(outer)"));
        assert_eq!(lines.next(), None);
    }

    #[test]
    fn invalid_inline_definitions_roll_back_their_names() {
        let output = execute(
            "(set-option :produce-unsat-cores true)
             (set-logic QF_BOOL)
             (declare-const p Bool)
             (assert (and forward (! p :named forward)))
             (define-fun bad ((x Bool)) Bool (! x :named captured))
             (assert (! p :named forward))
             (assert (! (not p) :named captured))
             (check-sat)
             (get-unsat-core)",
        );
        assert_eq!(
            output,
            "(error \"inline label `forward` is used before its definition\")\n\
             (error \"unknown symbol `x`\")\n\
             unsat\n(forward captured)\n"
        );
    }

    #[test]
    fn command_errors_preserve_state_and_start_only_options_are_enforced() {
        let output = execute(
            "(set-option :produce-assertions true)
             (get-assertions)
             (push 1)
             (set-logic QF_BOOL)
             (set-option :produce-models true)
             (get-option :produce-models)
             (check-sat)",
        );
        assert!(output.starts_with(
            "(error \"set-logic must be issued before declarations or solving\")\n\
                 (error \"set-logic must be issued before declarations or solving\")\n"
        ));
        assert!(output.contains(
            "(error \"option `:produce-models` can only be set before set-logic\")\nfalse\nsat\n"
        ));
    }

    #[test]
    fn oversized_bulk_push_fails_before_changing_the_scope_stack() {
        let output = execute(&format!(
            "(set-logic QF_BOOL)
             (push {})
             (get-info :assertion-stack-levels)
             (check-sat)",
            usize::MAX
        ));
        assert_eq!(
            output,
            "(error \"packed Boolean variable limit exceeded\")\n\
             (:assertion-stack-levels 0)\n\
             sat\n"
        );
    }

    #[test]
    fn rejected_assumption_lists_do_not_install_valid_prefix_encodings() {
        let baseline = execute(
            "(set-option :produce-models true)
             (set-logic QF_UF)
             (declare-const p Bool)
             (declare-const q Bool)
             (declare-sort U 0)
             (declare-const a U)
             (check-sat)
             (get-model)",
        );
        let after_error = execute(
            "(set-option :produce-models true)
             (set-logic QF_UF)
             (declare-const p Bool)
             (declare-const q Bool)
             (declare-sort U 0)
             (declare-const a U)
             (check-sat-assuming ((xor p q) a))
             (check-sat)
             (get-model)",
        );
        assert_eq!(
            after_error,
            format!("(error \"expected a term of sort Bool\")\n{baseline}")
        );
    }

    #[test]
    fn function_definition_typechecking_does_not_consume_model_values() {
        let baseline = execute(
            "(set-option :produce-models true)
             (set-logic QF_UF)
             (declare-sort U 0)
             (declare-const a U)
             (check-sat)
             (get-model)",
        );
        let after_error = execute(
            "(set-option :produce-models true)
             (set-logic QF_UF)
             (declare-sort U 0)
             (define-fun bad ((x U)) U true)
             (declare-const a U)
             (check-sat)
             (get-model)",
        );
        assert_eq!(
            after_error,
            format!(
                "(error \"definition of `bad` does not have its declared result sort\")\n\
                 {baseline}"
            )
        );

        let after_definition = execute(
            "(set-option :produce-models true)
             (set-logic QF_UF)
             (declare-sort U 0)
             (define-fun identity ((x U)) U x)
             (declare-const a U)
             (check-sat)
             (get-model)",
        );
        assert_eq!(after_definition, baseline);
    }

    #[test]
    fn rejected_term_commands_restore_the_term_arena() {
        let baseline = execute(
            "(set-option :produce-models true)
             (set-logic QF_UF)
             (declare-sort U 0)
             (declare-const a U)
             (declare-fun f (U) U)
             (declare-const b U)
             (check-sat)
             (get-model)",
        );
        let after_bad_definition = execute(
            "(set-option :produce-models true)
             (set-logic QF_UF)
             (declare-sort U 0)
             (declare-const a U)
             (declare-fun f (U) U)
             (define-const bad Bool (f a))
             (declare-const b U)
             (check-sat)
             (get-model)",
        );
        assert_eq!(
            after_bad_definition,
            format!("(error \"definition of `bad` does not have its declared sort\")\n{baseline}")
        );

        let after_bad_assertion = execute(
            "(set-option :produce-models true)
             (set-logic QF_UF)
             (declare-sort U 0)
             (declare-const a U)
             (declare-fun f (U) U)
             (assert (f a))
             (declare-const b U)
             (check-sat)
             (get-model)",
        );
        assert_eq!(
            after_bad_assertion,
            format!("(error \"expected a term of sort Bool\")\n{baseline}")
        );

        let checked_baseline = execute(
            "(set-option :produce-models true)
             (set-logic QF_UF)
             (declare-sort U 0)
             (declare-const a U)
             (declare-fun f (U) U)
             (check-sat)
             (declare-const b U)
             (check-sat)
             (get-model)",
        );
        let after_bad_value_query = execute(
            "(set-option :produce-models true)
             (set-logic QF_UF)
             (declare-sort U 0)
             (declare-const a U)
             (declare-fun f (U) U)
             (check-sat)
             (get-value ((f a) missing))
             (declare-const b U)
             (check-sat)
             (get-model)",
        );
        assert_eq!(
            after_bad_value_query,
            checked_baseline.replacen("sat\n", "sat\n(error \"unknown symbol `missing`\")\n", 1)
        );
    }

    #[test]
    fn reset_assertions_reinstalls_axioms_for_global_array_declarations() {
        let output = execute(
            "(set-option :global-declarations true)
             (set-logic QF_ABV)
             (declare-const a (Array (_ BitVec 1) (_ BitVec 1)))
             (declare-const i (_ BitVec 1))
             (declare-const value (_ BitVec 1))
             (assert (distinct (select (store a i value) i) value))
             (check-sat)
             (reset-assertions)
             (assert (distinct (select (store a i value) i) value))
             (check-sat)",
        );
        assert_eq!(output, "unsat\nunsat\n");
    }

    #[test]
    fn unsupported_standard_commands_report_unsupported() {
        let output = execute(
            "(set-logic QF_UF)
             (declare-sort-parameter A)
             (declare-datatype List ((nil) (cons (head A) (tail List))))
             (define-fun-rec loop ((x Bool)) Bool (loop x))
             (check-sat)",
        );
        assert_eq!(output, "unsupported\nunsupported\nunsupported\nsat\n");
    }

    #[test]
    fn unsupported_logic_is_honest_and_invalid_indexed_constants_do_not_poison_context() {
        let output = execute(
            "(set-logic QF_NIA)
             (set-logic QF_BV)
             (assert (= (_ bv16 4) #b0000))
             (check-sat)",
        );
        assert_eq!(
            output,
            "unsupported\n\
             (error \"decimal value does not fit in a 4-bit vector\")\n\
             sat\n"
        );
    }

    #[test]
    fn all_selects_the_supported_union_without_expanding_the_proof_claim() {
        let output = execute(
            "(set-logic ALL)
             (declare-const a (Array Int (_ BitVec 2)))
             (declare-const i Int)
             (declare-const value (_ BitVec 2))
             (declare-fun observe ((_ BitVec 2)) Int)
             (assert (= value #b01))
             (assert (distinct (select (store a i value) i) value))
             (assert (= (observe value) 7))
             (check-sat)
             (reset)
             (set-option :produce-proofs true)
             (set-logic ALL)
             (set-logic QF_BOOL)
             (check-sat)",
        );
        assert_eq!(output, "unsat\nunsupported\nsat\n");
    }

    #[test]
    fn theory_symbols_cannot_be_redeclared() {
        let output = execute(
            "(set-logic QF_BV)
             (declare-const bvadd (_ BitVec 4))
             (declare-const concat (_ BitVec 4))
             (declare-const okay (_ BitVec 4))
             (check-sat)",
        );
        assert_eq!(
            output,
            "(error \"symbol `bvadd` is already defined\")\n\
             (error \"symbol `concat` is already defined\")\n\
             sat\n"
        );
    }

    #[test]
    fn qf_uf_session_is_incremental_and_enforces_congruence() {
        let output = execute(
            "(set-option :produce-models true)
             (set-option :produce-unsat-cores true)
             (set-logic QF_UF)
             (declare-sort U 0)
             (declare-const a U)
             (declare-const b U)
             (declare-fun f (U) U)
             (assert (! (= a b) :named arguments))
             (push 1)
             (assert (distinct (f a) (f b)))
             (check-sat)
             (get-unsat-core)
             (pop 1)
             (check-sat)
             (get-value (a b (f a) (f b)))
             (get-model)",
        );
        assert!(output.starts_with("unsat\n(arguments)\nsat\n"));
        assert!(output.contains("((a @uc!0!0) (b @uc!0!0)"));
        let values = output
            .lines()
            .find(|line| line.starts_with("((a "))
            .expect("get-value response");
        let f_value = values
            .split_once("((f a) ")
            .and_then(|(_, suffix)| suffix.split_once(')'))
            .map(|(value, _)| value)
            .expect("f(a) value");
        assert!(
            values.contains(&format!("((f b) {f_value})")),
            "unexpected UF values:\n{output}"
        );
        assert!(output.contains("(define-fun a () U @uc!0!0)"));
        assert!(output.contains("(define-fun b () U @uc!0!0)"));
        assert!(output.contains("(define-fun f ((x!0 U)) U "));
    }

    #[test]
    fn qf_uf_definitions_are_typed_macros_and_follow_scope() {
        let output = execute(
            "(set-logic QF_UF)
             (declare-sort U 0)
             (declare-const a U)
             (declare-fun f (U) U)
             (define-fun twice ((x U)) U (f (f x)))
             (assert (distinct (twice a) (f (f a))))
             (check-sat)
             (push 1)
             (declare-fun local (U) U)
             (pop 1)
             (assert (= (local a) a))
             (check-sat)",
        );
        assert_eq!(
            output,
            "unsat\n(error \"unsupported operator `local`\")\nunsat\n"
        );
    }

    #[test]
    fn qf_ufbv_combines_congruence_with_bitvector_results() {
        let output = execute(
            "(set-logic QF_UFBV)
             (declare-sort U 0)
             (declare-const a U)
             (declare-const b U)
             (declare-fun color (U) (_ BitVec 4))
             (assert (= a b))
             (assert (distinct (color a) (color b)))
             (check-sat)",
        );
        assert_eq!(output, "unsat\n");
    }

    #[test]
    fn congruence_is_checked_for_bool_and_bitvector_only_signatures() {
        let bool_output = execute(
            "(set-logic QF_UF)
             (declare-const a Bool)
             (declare-const b Bool)
             (declare-fun p (Bool) Bool)
             (assert (= a b))
             (assert (xor (p a) (p b)))
             (check-sat)",
        );
        assert_eq!(bool_output, "unsat\n");

        let bitvector_output = execute(
            "(set-logic QF_UFBV)
             (declare-const x (_ BitVec 3))
             (declare-const y (_ BitVec 3))
             (declare-fun f ((_ BitVec 3)) (_ BitVec 2))
             (assert (= x y))
             (assert (distinct (f x) (f y)))
             (check-sat)",
        );
        assert_eq!(bitvector_output, "unsat\n");
    }

    #[test]
    fn get_value_extends_a_uf_model_for_terms_created_after_check_sat() {
        let output = execute(
            "(set-option :produce-models true)
             (set-logic QF_UF)
             (declare-sort U 0)
             (declare-const a U)
             (declare-const b U)
             (declare-fun f (U) U)
             (assert (= a b))
             (assert (distinct (f a) a))
             (check-sat)
             (get-value (a b (f a) (f b)))",
        );
        assert_eq!(
            output,
            "sat\n\
             ((a @uc!0!0) (b @uc!0!0) ((f a) @uc!0!1) ((f b) @uc!0!1))\n"
        );
    }

    #[test]
    fn qf_abv_store_select_and_extensionality_are_incremental() {
        let output = execute(
            "(set-logic QF_ABV)
             (declare-const a (Array (_ BitVec 1) (_ BitVec 2)))
             (declare-const b (Array (_ BitVec 1) (_ BitVec 2)))
             (assert (= (select a #b0) (select b #b0)))
             (assert (= (select a #b1) (select b #b1)))
             (push 1)
             (assert (distinct a b))
             (check-sat)
             (pop 1)
             (assert (distinct (select (store a #b0 #b11) #b0) #b11))
             (check-sat)",
        );
        assert_eq!(output, "unsat\nunsat\n");
    }

    #[test]
    fn qf_abv_proofs_cover_store_select_and_extensionality() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_ABV)
             (declare-const a (Array (_ BitVec 1) (_ BitVec 2)))
             (declare-const b (Array (_ BitVec 1) (_ BitVec 2)))
             (assert (= (select a #b0) (select b #b0)))
             (assert (= (select a #b1) (select b #b1)))
             (assert (distinct a b))
             (assert (distinct (select (store a #b0 #b11) #b0) #b11))
             (check-sat)
             (get-proof)",
        );
        assert!(output.starts_with("unsat\n(satrap-edrat :version 1 :logic QF_ABV"));
        assert!(output.contains("(theory "));
        assert!(output.ends_with("0\n\")\n"));
    }

    #[test]
    fn qf_abv_proofs_ignore_unrelated_internal_allocation_history() {
        let query = "
             (declare-const a (Array (_ BitVec 1) (_ BitVec 1)))
             (assert (distinct (select (store a #b0 #b1) #b0) #b1))
             (check-sat)
             (get-proof)";
        let baseline = execute(&format!(
            "(set-option :produce-proofs true)
             (set-logic QF_ABV)
             {query}"
        ));
        let shifted = execute(&format!(
            "(set-option :produce-proofs true)
             (set-logic QF_ABV)
             (declare-const unused (Array (_ BitVec 1) (_ BitVec 1)))
             (define-const unused-store (Array (_ BitVec 1) (_ BitVec 1))
               (store unused #b1 #b0))
             {query}"
        ));
        assert_eq!(baseline, shifted);
    }

    #[test]
    fn qf_abv_constant_arrays_have_standard_model_values() {
        let output = execute(
            "(set-option :produce-models true)
             (set-logic QF_ABV)
             (declare-const a (Array (_ BitVec 2) (_ BitVec 4)))
             (assert (= a ((as const (Array (_ BitVec 2) (_ BitVec 4))) #b0011)))
             (check-sat)
             (get-value (a (select a #b10)))
             (get-model)",
        );
        assert!(output.starts_with(
            "sat\n((a ((as const (Array (_ BitVec 2) (_ BitVec 4))) #b0011)) \
             ((select a #b10) #b0011))\n"
        ));
        assert!(output.contains(
            "(define-fun a () (Array (_ BitVec 2) (_ BitVec 4)) \
             ((as const (Array (_ BitVec 2) (_ BitVec 4))) #b0011))"
        ));
    }

    #[test]
    fn qf_aufbv_combines_arrays_uf_and_bitvectors() {
        let output = execute(
            "(set-logic QF_AUFBV)
             (declare-sort U 0)
             (declare-const a (Array (_ BitVec 2) U))
             (declare-const b (Array (_ BitVec 2) U))
             (declare-fun observe ((Array (_ BitVec 2) U)) (_ BitVec 3))
             (assert (= a b))
             (assert (distinct (observe a) (observe b)))
             (check-sat)",
        );
        assert_eq!(output, "unsat\n");
    }

    #[test]
    fn qf_aufbv_proofs_combine_arrays_uf_and_bitvectors() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_AUFBV)
             (declare-sort U 0)
             (declare-const value U)
             (declare-const a (Array (_ BitVec 1) U))
             (declare-const b (Array (_ BitVec 1) U))
             (declare-fun observe ((Array (_ BitVec 1) U)) (_ BitVec 2))
             (assert (= a b))
             (assert (distinct (observe a) (observe b)))
             (assert (distinct (select (store a #b0 value) #b0) value))
             (check-sat)
             (get-proof)",
        );
        assert!(output.starts_with("unsat\n(satrap-edrat :version 1 :logic QF_AUFBV"));
        assert!(output.contains("(theory "));
        assert!(output.ends_with("0\n\")\n"));
    }

    #[test]
    fn qf_idl_is_exact_incremental_and_uses_unbounded_integers() {
        let output = execute(
            "(set-option :produce-models true)
             (set-logic QF_IDL)
             (declare-const x Int)
             (declare-const y Int)
             (assert (<= (- x y) 10000000000000000000000000000000000000000))
             (check-sat)
             (get-value (x y (- x y)))
             (push 1)
             (assert (<= (- x y) 1))
             (assert (<= (- y x) (- 2)))
             (check-sat)
             (pop 1)
             (check-sat)",
        );
        let mut lines = output.lines();
        assert_eq!(lines.next(), Some("sat"));
        let values = lines.next().expect("get-value response");
        assert!(values.starts_with("((x "));
        assert!(values.contains(" (y "));
        assert!(values.contains(" ((- x y) "));
        assert_eq!(lines.next(), Some("unsat"));
        assert_eq!(lines.next(), Some("sat"));
    }

    #[test]
    fn qf_idl_proofs_include_negative_cycle_theory_lemmas() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_IDL)
             (declare-const x Int)
             (declare-const y Int)
             (assert (<= (- x y) 1))
             (assert (<= (- y x) (- 2)))
             (check-sat)
             (get-proof)",
        );
        assert!(output.starts_with("unsat\n(satrap-edrat :version 1 :logic QF_IDL"));
        assert!(output.contains(":premises (\"(<= (- x y) 1)\" \"(<= (- y x) (- 2))\")"));
        assert!(output.contains("(theory "));
        assert!(output.ends_with("0\n\")\n"));
    }

    #[test]
    fn qf_idl_proofs_cover_arithmetic_ite_conditions() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_IDL)
             (declare-const c Bool)
             (declare-const x Int)
             (declare-const y Int)
             (assert c)
             (assert (> (ite c x y) x))
             (check-sat)
             (get-proof)",
        );
        assert!(output.starts_with("unsat\n(satrap-edrat :version 1 :logic QF_IDL"));
        assert!(output.contains("(theory "));
        assert!(output.ends_with("0\n\")\n"));
    }

    #[test]
    fn qf_idl_proofs_ignore_unrelated_internal_allocation_history() {
        let query = "
             (declare-const x Int)
             (declare-const y Int)
             (assert (<= (- x y) 1))
             (assert (<= (- y x) (- 2)))
             (check-sat)
             (get-proof)";
        let baseline = execute(&format!(
            "(set-option :produce-proofs true)
             (set-logic QF_IDL)
             {query}"
        ));
        let shifted = execute(&format!(
            "(set-option :produce-proofs true)
             (set-logic QF_IDL)
             (declare-const unused Int)
             (define-const unused-offset Int (+ unused 17))
             {query}"
        ));
        assert_eq!(baseline, shifted);
    }

    #[test]
    fn qf_rdl_strict_cycles_are_unsatisfiable() {
        let output = execute(
            "(set-logic QF_RDL)
             (declare-const x Real)
             (declare-const y Real)
             (assert (< x y))
             (assert (<= y x))
             (check-sat)",
        );
        assert_eq!(output, "unsat\n");
    }

    #[test]
    fn qf_rdl_proofs_include_strict_negative_cycle_lemmas() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_RDL)
             (declare-const x Real)
             (declare-const y Real)
             (assert (< x y))
             (assert (<= y x))
             (check-sat)
             (get-proof)",
        );
        assert!(output.starts_with("unsat\n(satrap-edrat :version 1 :logic QF_RDL"));
        assert!(output.contains("(theory "));
        assert!(output.ends_with("0\n\")\n"));
    }

    #[test]
    fn qf_lra_proofs_include_exact_fourier_motzkin_lemmas() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_LRA)
             (declare-const x Real)
             (declare-const y Real)
             (assert (> (+ (* 2.0 x) y) 4.0))
             (assert (<= x 1.0))
             (assert (<= y 2.0))
             (check-sat)
             (get-proof)",
        );
        assert!(output.starts_with("unsat\n(satrap-edrat :version 1 :logic QF_LRA"));
        assert!(output.contains("(theory "));
        assert!(output.ends_with("0\n\")\n"));
    }

    #[test]
    fn qf_lra_proofs_cover_selected_arithmetic_ite_branches() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_LRA)
             (declare-const p Bool)
             (declare-const x Real)
             (declare-const y Real)
             (assert p)
             (assert (= x (ite p (+ (* 2.0 y) 1.0) 0.0)))
             (assert (> x (+ (* 2.0 y) 1.0)))
             (check-sat)
             (get-proof)",
        );
        assert!(output.starts_with("unsat\n(satrap-edrat :version 1 :logic QF_LRA"));
        assert!(output.contains("(theory "));
        assert!(output.ends_with("0\n\")\n"));
    }

    #[test]
    fn qf_lra_proofs_ignore_unrelated_internal_allocation_history() {
        let query = "
             (declare-const x Real)
             (declare-const y Real)
             (assert (> (+ (* 2.0 x) y) 4.0))
             (assert (<= x 1.0))
             (assert (<= y 2.0))
             (check-sat)
             (get-proof)";
        let baseline = execute(&format!(
            "(set-option :produce-proofs true)
             (set-logic QF_LRA)
             {query}"
        ));
        let shifted = execute(&format!(
            "(set-option :produce-proofs true)
             (set-logic QF_LRA)
             (declare-const unused Real)
             (define-const unused-offset Real (+ (* 7.0 unused) 11.0))
             {query}"
        ));
        assert_eq!(baseline, shifted);
    }

    #[test]
    fn qf_lia_proofs_include_exact_cooper_elimination_lemmas() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_LIA)
             (declare-const x Int)
             (declare-const y Int)
             (assert (= (+ (* 2 x) (* 4 y)) 1))
             (check-sat)
             (get-proof)",
        );
        assert!(output.starts_with("unsat\n(satrap-edrat :version 1 :logic QF_LIA"));
        assert!(output.contains("(theory "));
        assert!(output.ends_with("0\n\")\n"));
    }

    #[test]
    fn qf_lia_proofs_cover_selected_arithmetic_ite_branches() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_LIA)
             (declare-const p Bool)
             (declare-const x Int)
             (declare-const y Int)
             (assert p)
             (assert (= x (ite p (+ (* 2 y) 1) 0)))
             (assert (= x (* 2 y)))
             (check-sat)
             (get-proof)",
        );
        assert!(output.starts_with("unsat\n(satrap-edrat :version 1 :logic QF_LIA"));
        assert!(output.contains("(theory "));
        assert!(output.ends_with("0\n\")\n"));
    }

    #[test]
    fn qf_lia_proofs_ignore_unrelated_internal_allocation_history() {
        let query = "
             (declare-const x Int)
             (declare-const y Int)
             (assert (= (+ (* 2 x) (* 4 y)) 1))
             (check-sat)
             (get-proof)";
        let baseline = execute(&format!(
            "(set-option :produce-proofs true)
             (set-logic QF_LIA)
             {query}"
        ));
        let shifted = execute(&format!(
            "(set-option :produce-proofs true)
             (set-logic QF_LIA)
             (declare-const unused Int)
             (define-const unused-offset Int (+ (* 7 unused) 11))
             {query}"
        ));
        assert_eq!(baseline, shifted);
    }

    #[test]
    fn qf_ufidl_proofs_combine_congruence_with_exact_integer_arithmetic() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_UFIDL)
             (declare-const x Int)
             (declare-fun f (Int) Int)
             (assert (= x 0))
             (assert (= (f x) 0))
             (assert (= (f 0) 1))
             (check-sat)
             (get-proof)",
        );
        assert!(output.starts_with("unsat\n(satrap-edrat :version 1 :logic QF_UFIDL"));
        assert!(output.contains("(theory "));
        assert!(output.ends_with("0\n\")\n"));
    }

    #[test]
    fn qf_uflia_proofs_combine_congruence_with_cooper_elimination() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_UFLIA)
             (declare-const x Int)
             (declare-const y Int)
             (declare-fun f (Int) Int)
             (assert (= x 0))
             (assert (= (f x) (* 2 y)))
             (assert (= (f 0) 1))
             (check-sat)
             (get-proof)",
        );
        assert!(output.starts_with("unsat\n(satrap-edrat :version 1 :logic QF_UFLIA"));
        assert!(output.contains("(theory "));
        assert!(output.ends_with("0\n\")\n"));
    }

    #[test]
    fn qf_uflra_proofs_combine_congruence_with_fourier_motzkin() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_UFLRA)
             (declare-const x Real)
             (declare-fun f (Real) Real)
             (assert (= x 0.0))
             (assert (> (f x) (f 0.0)))
             (check-sat)
             (get-proof)",
        );
        assert!(output.starts_with("unsat\n(satrap-edrat :version 1 :logic QF_UFLRA"));
        assert!(output.contains("(theory "));
        assert!(output.ends_with("0\n\")\n"));
    }

    #[test]
    fn qf_auflia_proofs_combine_extensional_arrays_uf_and_integer_arithmetic() {
        let output = execute(
            "(set-option :produce-proofs true)
             (set-logic QF_AUFLIA)
             (declare-const a (Array Int Int))
             (declare-const i Int)
             (declare-fun observe ((Array Int Int)) Int)
             (assert
               (distinct
                 (observe (store a i (select a i)))
                 (observe a)))
             (check-sat)
             (get-proof)",
        );
        assert!(
            output.starts_with("unsat\n(satrap-edrat :version 1 :logic QF_AUFLIA"),
            "unexpected QF_AUFLIA proof output:\n{output}"
        );
        assert!(output.contains("(theory "));
        assert!(output.ends_with("0\n\")\n"));
    }

    #[test]
    fn arithmetic_combination_proofs_ignore_unrelated_allocation_history() {
        let query = "
             (declare-const x Int)
             (declare-const y Int)
             (declare-fun f (Int) Int)
             (assert (= x 0))
             (assert (= (f x) (* 2 y)))
             (assert (= (f 0) 1))
             (check-sat)
             (get-proof)";
        let baseline = execute(&format!(
            "(set-option :produce-proofs true)
             (set-logic QF_UFLIA)
             {query}"
        ));
        let shifted = execute(&format!(
            "(set-option :produce-proofs true)
             (set-logic QF_UFLIA)
             (declare-const unused Int)
             (declare-fun unused-function (Int) Int)
             (define-const unused-application Int (unused-function unused))
             {query}"
        ));
        assert_eq!(baseline, shifted);
    }

    #[test]
    fn qf_lra_fourier_motzkin_handles_general_linear_constraints_and_models() {
        let output = execute(
            "(set-option :produce-models true)
             (set-logic QF_LRA)
             (declare-const x Real)
             (declare-const y Real)
             (assert (> x 0))
             (assert (> y 0))
             (assert (= (+ x y) 1))
             (check-sat)
             (get-value (x y (+ x y)))
             (push 1)
             (assert (> (+ x y) 3))
             (assert (<= x 1))
             (assert (<= y 1))
             (check-sat)
             (pop 1)
             (check-sat)",
        );
        let mut lines = output.lines();
        assert_eq!(lines.next(), Some("sat"));
        assert_eq!(
            lines.next(),
            Some("((x (/ 1.0 2.0)) (y (/ 1.0 2.0)) ((+ x y) 1.0))")
        );
        assert_eq!(lines.next(), Some("unsat"));
        assert_eq!(lines.next(), Some("sat"));
    }

    #[test]
    fn qf_lra_model_validation_checks_the_selected_ite_branch() {
        let output = execute(
            "(set-option :produce-models true)
             (set-logic QF_LRA)
             (declare-const p Bool)
             (declare-const x Real)
             (assert p)
             (assert (= x (ite p 1.0 2.0)))
             (check-sat)
             (get-value (p x (ite p 1.0 2.0)))",
        );
        assert_eq!(output, "sat\n((p true) (x 1.0) ((ite p 1.0 2.0) 1.0))\n");
    }

    #[test]
    fn qf_lia_decides_general_linear_constraints_and_exact_models() {
        let output = execute(
            "(set-option :produce-models true)
             (set-logic QF_LIA)
             (declare-const x Int)
             (declare-const y Int)
             (assert (= (+ (* 2 x) (* 3 y)) 7))
             (assert (>= x 0))
             (assert (>= y 0))
             (check-sat)
             (get-value (x y (+ (* 2 x) (* 3 y))))
             (push 1)
             (assert (= (* 2 (+ x y)) 1))
             (check-sat)
             (pop 1)
             (check-sat)",
        );
        let mut lines = output.lines();
        assert_eq!(lines.next(), Some("sat"));
        let values = lines.next().expect("get-value response");
        assert!(values.starts_with("((x "));
        assert!(values.contains(" (y "));
        assert!(values.ends_with(" 7))"));
        assert_eq!(lines.next(), Some("unsat"));
        assert_eq!(lines.next(), Some("sat"));
    }

    #[test]
    fn qf_ufidl_shares_integer_equalities_with_congruence() {
        let output = execute(
            "(set-logic QF_UFIDL)
             (declare-const x Int)
             (declare-const y Int)
             (declare-fun f (Int) Int)
             (assert (<= (- x y) 0))
             (assert (<= (- y x) 0))
             (assert (distinct (f x) (f y)))
             (check-sat)",
        );
        assert_eq!(output, "unsat\n");
    }

    #[test]
    fn qf_uflia_combines_general_integer_arithmetic_and_uf() {
        let output = execute(
            "(set-option :produce-models true)
             (set-logic QF_UFLIA)
             (declare-sort U 0)
             (declare-const x Int)
             (declare-const y Int)
             (declare-fun f (Int) U)
             (declare-fun value (U) Int)
             (assert (= (+ (* 2 x) (* 3 y)) 5))
             (assert (= x y))
             (check-sat)
             (get-value (x y (value (f x)) (value (f y))))
             (push 1)
             (assert (distinct (value (f x)) (value (f y))))
             (check-sat)
             (pop 1)
             (check-sat)",
        );
        let mut lines = output.lines();
        assert_eq!(lines.next(), Some("sat"));
        let values = lines.next().expect("get-value response");
        assert!(values.starts_with("((x 1) (y 1)"));
        assert_eq!(lines.next(), Some("unsat"));
        assert_eq!(lines.next(), Some("sat"));
    }

    #[test]
    fn popped_arithmetic_applications_do_not_pollute_function_models() {
        let output = execute(
            "(set-option :produce-models true)
             (set-logic QF_UFLIA)
             (declare-const x Int)
             (declare-const y Int)
             (declare-fun f (Int) Int)
             (push 1)
             (assert (= y 0))
             (assert (= (f y) 7))
             (check-sat)
             (pop 1)
             (assert (= x 0))
             (assert (= (f x) 3))
             (check-sat)
             (get-value ((f y)))
             (get-model)",
        );
        assert!(
            output.starts_with("sat\nsat\n(((f y) 3))\n"),
            "unexpected incremental model output:\n{output}"
        );
        assert!(output.contains("(define-fun f ((x!0 Int)) Int (ite (= x!0 0) 3 3))"));
    }

    #[test]
    fn qf_uflra_shares_exact_real_equalities_with_congruence() {
        let output = execute(
            "(set-logic QF_UFLRA)
             (declare-const x Real)
             (declare-const y Real)
             (declare-fun f (Real) Real)
             (assert (= (+ (* 2.0 x) y) (/ 3.0 2.0)))
             (assert (= x y))
             (assert (> (f x) (f y)))
             (check-sat)",
        );
        assert_eq!(output, "unsat\n");
    }

    #[test]
    fn qf_auflia_combines_extensional_arrays_uf_and_integer_indices() {
        let output = execute(
            "(set-logic QF_AUFLIA)
             (declare-const a (Array Int Int))
             (declare-const b (Array Int Int))
             (declare-const i Int)
             (declare-const j Int)
             (declare-fun observe ((Array Int Int)) Int)
             (push 1)
             (assert (= i j))
             (assert (distinct (select (store a i 5) j) 5))
             (check-sat)
             (pop 1)
             (assert (= a b))
             (assert (distinct (observe a) (observe b)))
             (check-sat)",
        );
        assert_eq!(output, "unsat\nunsat\n");
    }

    #[test]
    fn arithmetic_ite_conditions_are_in_theory_relevance_closure() {
        let output = execute(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (declare-const y Int)
             (assert (= x 0))
             (assert (= y 1))
             (assert (= (ite (< x y) 0 1) 1))
             (check-sat)",
        );
        assert_eq!(output, "unsat\n");
    }

    #[test]
    fn nonlinear_integer_arithmetic_remains_an_explicit_error() {
        let output = execute(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (declare-const y Int)
             (assert (= (* x y) 2))",
        );
        assert_eq!(
            output,
            "(error \"nonlinear multiplication is outside the supported logics\")\n"
        );
    }

    #[test]
    fn popped_general_integer_atoms_do_not_poison_later_queries() {
        let output = execute(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (declare-const y Int)
             (push 1)
             (assert (= (+ x y) 1))
             (check-sat)
             (pop 1)
             (assert (= x 0))
             (check-sat)",
        );
        assert_eq!(output, "sat\nsat\n");
    }

    #[test]
    fn exit_observes_print_success_and_reserved_names_remain_quoted() {
        let output = execute(
            "(set-option :print-success true)
             (set-option :produce-models true)
             (set-logic QF_BOOL)
             (declare-const |let| Bool)
             (check-sat)
             (get-model)
             (exit)",
        );
        assert!(output.contains("(define-fun |let| () Bool false)"));
        assert!(output.ends_with(")\nsuccess\n"));
    }

    #[test]
    fn standard_output_channels_redirect_immediately_and_append() {
        let regular_path = output_test_path("regular");
        let diagnostic_path = output_test_path("diagnostic");
        fs::write(&regular_path, "existing\n").unwrap();
        let _ = fs::remove_file(&diagnostic_path);
        let regular = regular_path.to_string_lossy();
        let diagnostic = diagnostic_path.to_string_lossy();
        let output = execute(&format!(
            "(set-option :print-success true)
             (set-option :diagnostic-output-channel \"{diagnostic}\")
             (get-option :diagnostic-output-channel)
             (set-option :regular-output-channel \"{regular}\")
             (echo \"redirected\")
             (get-option :regular-output-channel)
             (set-option :regular-output-channel \"stdout\")
             (echo \"primary\")
             (exit)"
        ));
        let redirected = fs::read_to_string(&regular_path).unwrap();
        let diagnostic_metadata = fs::metadata(&diagnostic_path).unwrap();
        fs::remove_file(&regular_path).unwrap();
        fs::remove_file(&diagnostic_path).unwrap();

        assert_eq!(
            output,
            format!("success\nsuccess\n\"{diagnostic}\"\nsuccess\n\"primary\"\nsuccess\n")
        );
        assert_eq!(
            redirected,
            format!("existing\nsuccess\n\"redirected\"\n\"{regular}\"\n")
        );
        assert_eq!(diagnostic_metadata.len(), 0);
    }

    #[test]
    fn failed_output_redirection_rolls_back_and_continues() {
        let missing = output_test_path("missing")
            .with_extension("dir")
            .join("output.log");
        let missing = missing.to_string_lossy();
        let output = execute(&format!(
            "(set-option :print-success true)
             (set-option :regular-output-channel \"{missing}\")
             (get-option :regular-output-channel)
             (set-option :diagnostic-output-channel \"{missing}\")
             (get-option :diagnostic-output-channel)
             (echo \"still-open\")
             (exit)"
        ));

        assert!(output.starts_with("success\n(error \"could not open regular output channel"));
        assert!(output.contains("\n\"stdout\"\n"));
        assert!(output.contains("\n(error \"could not open diagnostic output channel"));
        assert!(output.ends_with("\n\"stderr\"\n\"still-open\"\nsuccess\n"));
    }
}
