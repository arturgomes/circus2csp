-- THIS IS A GENERATED FILE - DO NOT EDIT!
-- Haskell syntax is only superficial.

module Generated_Adapt where

raw_adaption_table = [(Haskell "Prelude.Eq" (Class (RawClassInfo { superclasses = [], classVar = "a", methods = [("Prelude.(==)", "a -> a -> bool"), ("Prelude.(/=)", "a -> a -> bool")] })), Isabelle "Prelude.eq" (Class (RawClassInfo { superclasses = [], classVar = "a", methods = [("Prelude.(==)", "a -> a -> bool"), ("Prelude.(/=)", "a -> a -> bool")] }))),
  (Haskell "Prelude.Ord" (Class (RawClassInfo { superclasses = [], classVar = "a", methods = [("Prelude.(<=)", "a -> a -> bool"), ("Prelude.(<)", "a -> a -> bool")] })), Isabelle "Prelude.ord" (Class (RawClassInfo { superclasses = [], classVar = "a", methods = [("Prelude.(<=)", "a -> a -> bool"), ("Prelude.(<)", "a -> a -> bool")] }))),
  (Haskell "Prelude.Show" (Class (RawClassInfo { superclasses = [], classVar = "a", methods = [("Prelude.show", "a -> String")] })), Isabelle "Prelude.print" (Class (RawClassInfo { superclasses = [], classVar = "a", methods = [("Prelude.show", "a -> String")] }))),
  (Haskell "Prelude.Num" (Class (RawClassInfo { superclasses = [], classVar = "a", methods = [] })), Isabelle "Prelude.num" (Class (RawClassInfo { superclasses = [], classVar = "a", methods = [] }))),
  (Haskell "Prelude.Bool" Type, Isabelle "HOL.bool" Type),
  (Haskell "Prelude.UnitTyCon" Type, Isabelle "Product_Type.unit" Type),
  (Haskell "Prelude.PairTyCon" Type, Isabelle "Product_Type.prod" Type),
  (Haskell "Prelude.ListTyCon" Type, Isabelle "List.list" Type),
  (Haskell "Prelude.Maybe" Type, Isabelle "Option.option" Type),
  (Haskell "Prelude.Char" Type, Isabelle "String.char" Type),
  (Haskell "Prelude.String" Type, Isabelle "String.string" Type),
  (Haskell "Prelude.Int" Type, Isabelle "Int.int" Type),
  (Haskell "Prelude.Integer" Type, Isabelle "Int.int" Type),
  (Haskell "Prelude.True" Function, Isabelle "HOL.True" Function),
  (Haskell "Prelude.False" Function, Isabelle "HOL.False" Function),
  (Haskell "Prelude.not" Function, Isabelle "HOL.Not" Function),
  (Haskell "Prelude.(&&)" Function, Isabelle "&" (InfixOp RightAssoc 35)),
  (Haskell "Prelude.(||)" Function, Isabelle "|" (InfixOp RightAssoc 30)),
  (Haskell "Prelude._|_" Function, Isabelle "HOL.undefined" Function),
  (Haskell "Prelude.error" Function, Isabelle "Prelude.error" Function),
  (Haskell "Prelude.($)" Function, Isabelle "$" (InfixOp RightAssoc 60)),
  (Haskell "Prelude.const" Function, Isabelle "Prelude.const" Function),
  (Haskell "Prelude.id" Function, Isabelle "Fun.id" Function),
  (Haskell "Prelude.(.)" Function, Isabelle "o" (InfixOp LeftAssoc 55)),
  (Haskell "Prelude.curry" Function, Isabelle "Prelude.curry" Function),
  (Haskell "Prelude.uncurry" Function, Isabelle "Prelude.uncurry" Function),
  (Haskell "Prelude.(==)" Function, Isabelle "Prelude.eq_class.eq" Function),
  (Haskell "Prelude.(/=)" Function, Isabelle "Prelude.eq_class.not_eq" Function),
  (Haskell "Prelude.(())" Function, Isabelle "Product_Type.Unity" Function),
  (Haskell "Prelude.PairDataCon" Function, Isabelle "Product_Type.Pair" Function),
  (Haskell "Prelude.fst" Function, Isabelle "Product_Type.prod.fst" Function),
  (Haskell "Prelude.snd" Function, Isabelle "Product_Type.prod.snd" Function),
  (Haskell "Prelude.([])" Function, Isabelle "List.list.Nil" Function),
  (Haskell "Prelude.(:)" Function, Isabelle "#" (InfixOp RightAssoc 65)),
  (Haskell "Prelude.null" Function, Isabelle "Prelude.null" Function),
  (Haskell "Prelude.head" Function, Isabelle "List.list.hd" Function),
  (Haskell "Prelude.tail" Function, Isabelle "List.list.tl" Function),
  (Haskell "Prelude.map" Function, Isabelle "List.list.map" Function),
  (Haskell "Prelude.filter" Function, Isabelle "List.filter" Function),
  (Haskell "Prelude.(++)" Function, Isabelle "@" (InfixOp RightAssoc 65)),
  (Haskell "Prelude.concat" Function, Isabelle "List.concat" Function),
  (Haskell "Prelude.reverse" Function, Isabelle "List.rev" Function),
  (Haskell "Prelude.elem" Function, Isabelle "Prelude.member" Function),
  (Haskell "Prelude.notElem" Function, Isabelle "Prelude.not_member" Function),
  (Haskell "Prelude.replicate" Function, Isabelle "Prelude.replicate" Function),
  (Haskell "Prelude.(!!)" Function, Isabelle "Prelude.nth" Function),
  (Haskell "Prelude.length" Function, Isabelle "Prelude.length" Function),
  (Haskell "Prelude.any" Function, Isabelle "List.list_ex" Function),
  (Haskell "Prelude.all" Function, Isabelle "List.list_all" Function),
  (Haskell "Prelude.zip" Function, Isabelle "List.zip" Function),
  (Haskell "Prelude.foldl" Function, Isabelle "List.foldl" Function),
  (Haskell "Prelude.foldr" Function, Isabelle "List.foldr" Function),
  (Haskell "Prelude.Nothing" Function, Isabelle "Option.option.None" Function),
  (Haskell "Prelude.Just" Function, Isabelle "Option.option.Some" Function),
  (Haskell "Prelude.maybe" Function, Isabelle "Prelude.maybe" Function),
  (Haskell "Prelude.show" Function, Isabelle "Prelude.print_class.print" Function),
  (Haskell "Prelude.(+)" Function, Isabelle "+" (InfixOp LeftAssoc 65)),
  (Haskell "Prelude.(*)" Function, Isabelle "*" (InfixOp LeftAssoc 70)),
  (Haskell "Prelude.negate" Function, Isabelle "Groups.uminus_class.uminus" Function),
  (Haskell "Prelude.(-)" Function, Isabelle "-" (InfixOp LeftAssoc 65)),
  (Haskell "Prelude.(<)" Function, Isabelle "<" (InfixOp NoneAssoc 50)),
  (Haskell "Prelude.(<=)" Function, Isabelle "<=" (InfixOp NoneAssoc 50)),
  (Haskell "Prelude.(>)" Function, Isabelle ">" (InfixOp NoneAssoc 50)),
  (Haskell "Prelude.(>=)" Function, Isabelle ">=" (InfixOp NoneAssoc 50)),
  (Haskell "Prelude.abs" Function, Isabelle "Groups.abs_class.abs" Function),
  (Haskell "Prelude.sgn" Function, Isabelle "Groups.sgn_class.sgn" Function),
  (Haskell "Prelude.fromInteger" Function, Isabelle "Int.ring_1_class.of_int" Function),
  (Haskell "Prelude.divMod" Function, Isabelle "Divides.divmod_int" Function),
  (Haskell "Prelude.min" Function, Isabelle "Orderings.ord_class.min" Function),
  (Haskell "Prelude.max" Function, Isabelle "Orderings.ord_class.max" Function)]

reserved_keywords = ["!",
  "!!",
  "%",
  "(",
  ")",
  "+",
  ",",
  "--",
  ".",
  "..",
  "/",
  ":",
  "::",
  ";",
  "<",
  "<=",
  "=",
  "==",
  "=>",
  "?",
  "ML",
  "ML_command",
  "ML_file",
  "ML_prf",
  "ML_val",
  "SML_export",
  "SML_file",
  "SML_import",
  "[",
  "\\<equiv>",
  "\\<leftharpoondown>",
  "\\<rightharpoonup>",
  "\\<rightleftharpoons>",
  "\\<subseteq>",
  "]",
  "abbreviation",
  "also",
  "and",
  "apply",
  "apply_end",
  "assume",
  "assumes",
  "attach",
  "attribute_setup",
  "axiomatization",
  "back",
  "begin",
  "binder",
  "bnf",
  "bundle",
  "by",
  "case",
  "chapter",
  "checking",
  "class",
  "class_deps",
  "class_instance",
  "class_relation",
  "codatatype",
  "code_datatype",
  "code_deps",
  "code_identifier",
  "code_module",
  "code_monad",
  "code_pred",
  "code_printing",
  "code_reflect",
  "code_reserved",
  "code_thms",
  "coinductive",
  "coinductive_set",
  "constant",
  "constrains",
  "consts",
  "context",
  "corollary",
  "datatype",
  "datatype_compat",
  "datatypes",
  "declaration",
  "declare",
  "def",
  "default_sort",
  "defer",
  "defines",
  "definition",
  "defs",
  "display_drafts",
  "done",
  "end",
  "experiment",
  "export_code",
  "extract",
  "extract_type",
  "file",
  "finally",
  "find_consts",
  "find_theorems",
  "find_unused_assms",
  "fix",
  "fixes",
  "for",
  "free_constructors",
  "from",
  "full_prf",
  "fun",
  "fun_cases",
  "function",
  "functions",
  "functor",
  "guess",
  "have",
  "header",
  "help",
  "hence",
  "hide_class",
  "hide_const",
  "hide_fact",
  "hide_type",
  "identifier",
  "if",
  "imports",
  "in",
  "include",
  "includes",
  "including",
  "inductive",
  "inductive_cases",
  "inductive_set",
  "inductive_simps",
  "infix",
  "infixl",
  "infixr",
  "instance",
  "instantiation",
  "interpret",
  "interpretation",
  "is",
  "judgment",
  "keywords",
  "lemma",
  "lemmas",
  "let",
  "lift_definition",
  "lifting_forget",
  "lifting_update",
  "local_setup",
  "locale",
  "locale_deps",
  "method_setup",
  "module_name",
  "monos",
  "moreover",
  "morphisms",
  "named_theorems",
  "next",
  "nitpick",
  "nitpick_params",
  "no_notation",
  "no_syntax",
  "no_translations",
  "no_type_notation",
  "nonterminal",
  "notation",
  "note",
  "notepad",
  "notes",
  "obtain",
  "obtains",
  "old_rep_datatype",
  "oops",
  "open",
  "oracle",
  "output",
  "overloaded",
  "overloading",
  "parametric",
  "parse_ast_translation",
  "parse_translation",
  "partial_function",
  "pervasive",
  "prefer",
  "presume",
  "prf",
  "primcorec",
  "primcorecursive",
  "primrec",
  "print_ML_antiquotations",
  "print_abbrevs",
  "print_antiquotations",
  "print_ast_translation",
  "print_attributes",
  "print_bnfs",
  "print_bundles",
  "print_case_translations",
  "print_cases",
  "print_claset",
  "print_classes",
  "print_codeproc",
  "print_codesetup",
  "print_coercions",
  "print_commands",
  "print_context",
  "print_defn_rules",
  "print_dependencies",
  "print_facts",
  "print_induct_rules",
  "print_inductives",
  "print_interps",
  "print_locale",
  "print_locales",
  "print_methods",
  "print_options",
  "print_orders",
  "print_quot_maps",
  "print_quotconsts",
  "print_quotients",
  "print_quotientsQ3",
  "print_quotmapsQ3",
  "print_rules",
  "print_simpset",
  "print_state",
  "print_statement",
  "print_syntax",
  "print_term_bindings",
  "print_theorems",
  "print_theory",
  "print_trans_rules",
  "print_translation",
  "private",
  "proof",
  "prop",
  "qed",
  "qualified",
  "quickcheck",
  "quickcheck_generator",
  "quickcheck_params",
  "quotient_definition",
  "quotient_type",
  "realizability",
  "realizers",
  "record",
  "schematic_corollary",
  "schematic_lemma",
  "schematic_theorem",
  "section",
  "setup",
  "setup_lifting",
  "show",
  "shows",
  "simproc_setup",
  "sledgehammer",
  "sledgehammer_params",
  "smt_status",
  "solve_direct",
  "sorry",
  "specification",
  "structure",
  "subclass",
  "sublocale",
  "subsection",
  "subsubsection",
  "syntax",
  "syntax_declaration",
  "term",
  "termination",
  "text",
  "text_raw",
  "then",
  "theorem",
  "theorems",
  "theory",
  "thm",
  "thm_deps",
  "thus",
  "thy_deps",
  "translations",
  "try",
  "try0",
  "txt",
  "typ",
  "type_class",
  "type_constructor",
  "type_notation",
  "type_synonym",
  "typed_print_translation",
  "typedecl",
  "typedef",
  "ultimately",
  "unchecked",
  "unfolding",
  "unused_thms",
  "using",
  "value",
  "values",
  "welcome",
  "where",
  "with",
  "write",
  "{",
  "|",
  "}"]

used_const_names = ["Above",
  "AboveS",
  "Abs_Integ",
  "Abs_Nat",
  "Abs_char",
  "Abs_ffun",
  "Abs_ffun_pre_ffun",
  "Abs_filter",
  "Abs_finite_1",
  "Abs_finite_2",
  "Abs_finite_3",
  "Abs_finite_4",
  "Abs_finite_4_pre_finite_4",
  "Abs_finite_5",
  "Abs_finite_5_pre_finite_5",
  "Abs_fun_box",
  "Abs_int",
  "Abs_lazy_sequence",
  "Abs_list",
  "Abs_narrowing_cons",
  "Abs_narrowing_cons_pre_narrowing_cons",
  "Abs_narrowing_term",
  "Abs_narrowing_term_pre_narrowing_term",
  "Abs_narrowing_type",
  "Abs_nibble",
  "Abs_nibble_pre_nibble",
  "Abs_num",
  "Abs_option",
  "Abs_pair_box",
  "Abs_pred",
  "Abs_prod",
  "Abs_property",
  "Abs_property_pre_property",
  "Abs_property_pre_property_bdT",
  "Abs_seq",
  "Abs_seq_pre_seq",
  "Abs_sum",
  "Abs_sumbool",
  "Abs_term",
  "Abs_three_valued",
  "Abs_tuple_isomorphism",
  "Abs_tuple_isomorphism_pre_tuple_isomorphism",
  "Abs_typerep",
  "Abs_unit",
  "Abs_unknown",
  "Abs_word",
  "All",
  "Babs",
  "Ball",
  "Bex",
  "Bex1_rel",
  "Bleast",
  "Chains",
  "Char",
  "Collect",
  "Cons",
  "Domain",
  "Domainp",
  "Eps",
  "Ex",
  "Ex1",
  "Existential",
  "False",
  "Field",
  "Func",
  "Func_map",
  "Greatest",
  "GreatestM",
  "INFIMUM",
  "Id",
  "Id_on",
  "If",
  "Image",
  "Inf",
  "Inf_class",
  "Inf_fin",
  "Inl",
  "Inl_Rep",
  "Inr",
  "Inr_Rep",
  "Ints",
  "Lazy_Sequence",
  "Least",
  "LeastM",
  "Left",
  "Let",
  "ListMem",
  "Max",
  "Min",
  "NO_MATCH",
  "Narrowing_sum_of_products",
  "Nat",
  "Nats",
  "Nibble0",
  "Nibble1",
  "Nibble2",
  "Nibble3",
  "Nibble4",
  "Nibble5",
  "Nibble6",
  "Nibble7",
  "Nibble8",
  "Nibble9",
  "NibbleA",
  "NibbleB",
  "NibbleC",
  "NibbleD",
  "NibbleE",
  "NibbleF",
  "Nil",
  "None",
  "Not",
  "Pair",
  "Pair_Rep",
  "Pow",
  "Powp",
  "Property",
  "Quot_True",
  "Quotient",
  "Quotient3",
  "Random_graph",
  "Random_rel",
  "Random_sumC",
  "Range",
  "Rangep",
  "Rep_Integ",
  "Rep_Nat",
  "Rep_char",
  "Rep_ffun",
  "Rep_ffun_pre_ffun",
  "Rep_filter",
  "Rep_finite_1",
  "Rep_finite_2",
  "Rep_finite_3",
  "Rep_finite_4",
  "Rep_finite_4_pre_finite_4",
  "Rep_finite_5",
  "Rep_finite_5_pre_finite_5",
  "Rep_fun_box",
  "Rep_int",
  "Rep_lazy_sequence",
  "Rep_list",
  "Rep_narrowing_cons",
  "Rep_narrowing_cons_pre_narrowing_cons",
  "Rep_narrowing_term",
  "Rep_narrowing_term_pre_narrowing_term",
  "Rep_narrowing_type",
  "Rep_nibble",
  "Rep_nibble_pre_nibble",
  "Rep_num",
  "Rep_option",
  "Rep_pair_box",
  "Rep_pred",
  "Rep_prod",
  "Rep_property",
  "Rep_property_pre_property",
  "Rep_property_pre_property_bdT",
  "Rep_seq",
  "Rep_seq_pre_seq",
  "Rep_sum",
  "Rep_sumbool",
  "Rep_term",
  "Rep_three_valued",
  "Rep_tuple_isomorphism",
  "Rep_tuple_isomorphism_pre_tuple_isomorphism",
  "Rep_typerep",
  "Rep_unit",
  "Rep_unknown",
  "Rep_word",
  "Respects",
  "Right",
  "STR",
  "SUPREMUM",
  "Sigma",
  "Some",
  "Suc",
  "Suc_Rep",
  "Sup",
  "Sup_class",
  "Sup_fin",
  "THE_default",
  "The",
  "True",
  "Trueprop",
  "Under",
  "UnderS",
  "Unity",
  "Universal",
  "Zero_Rep",
  "ab_group_add_class",
  "ab_semigroup_add_class",
  "ab_semigroup_mult_class",
  "abel_semigroup",
  "abel_semigroup_axioms",
  "abort_Bleast",
  "above",
  "aboveS",
  "abs",
  "abs_class",
  "abs_if_class",
  "acyclic",
  "adjust",
  "adm_wf",
  "antimono",
  "antisym",
  "apfst",
  "append",
  "apsnd",
  "around_zero_graph",
  "around_zero_rel",
  "around_zero_sumC",
  "asym",
  "asymp",
  "atLeast",
  "atLeastAtMost",
  "atLeastLessThan",
  "atMost",
  "at_bot",
  "at_top",
  "bacc",
  "bd_pre_property",
  "bi_total",
  "bi_unique",
  "bij_betw",
  "boolean_algebra_class",
  "bot",
  "bot_class",
  "bounded_forall",
  "bounded_forall_class",
  "bounded_lattice_bot_class",
  "bounded_lattice_class",
  "bounded_lattice_top_class",
  "bounded_semilattice_inf_top_class",
  "bounded_semilattice_sup_bot_class",
  "bsqr",
  "butlast",
  "can_select",
  "cancel_ab_semigroup_add_class",
  "cancel_comm_monoid_add_class",
  "cancel_semigroup_add_class",
  "card",
  "cardSuc",
  "card_UNIV",
  "card_of",
  "card_order_on",
  "case_abs",
  "case_bool",
  "case_cfun",
  "case_char",
  "case_cons",
  "case_elem",
  "case_ffun",
  "case_finite_1",
  "case_finite_2",
  "case_finite_3",
  "case_finite_4",
  "case_finite_5",
  "case_fun_box",
  "case_guard",
  "case_lazy_sequence",
  "case_list",
  "case_narrowing_cons",
  "case_narrowing_term",
  "case_narrowing_type",
  "case_nat",
  "case_natural",
  "case_nibble",
  "case_nil",
  "case_num",
  "case_option",
  "case_pair_box",
  "case_pred",
  "case_prod",
  "case_property",
  "case_seq",
  "case_sum",
  "case_sumbool",
  "case_term",
  "case_three_valued",
  "case_tuple_isomorphism",
  "case_typerep",
  "case_unit",
  "case_unknown",
  "case_word",
  "ccpo_class",
  "chain_subset",
  "chains",
  "char_of_nat",
  "check_all_class",
  "check_all_n_lists_graph",
  "check_all_n_lists_rel",
  "check_all_n_lists_sumC",
  "check_all_subsets_graph",
  "check_all_subsets_rel",
  "check_all_subsets_sumC",
  "cofinal",
  "cofinite",
  "comm_monoid",
  "comm_monoid_add_class",
  "comm_monoid_axioms",
  "comm_monoid_diff_class",
  "comm_monoid_list",
  "comm_monoid_list_set",
  "comm_monoid_mult_class",
  "comm_monoid_set",
  "comm_ring_1_class",
  "comm_ring_class",
  "comm_semiring_0_cancel_class",
  "comm_semiring_0_class",
  "comm_semiring_1_cancel_class",
  "comm_semiring_1_cancel_crossproduct_class",
  "comm_semiring_1_class",
  "comm_semiring_1_diff_distrib_class",
  "comm_semiring_class",
  "comp",
  "comp_fun_commute",
  "comp_fun_idem",
  "comp_fun_idem_axioms",
  "compat",
  "complete_boolean_algebra_class",
  "complete_distrib_lattice_class",
  "complete_lattice_class",
  "complete_linorder_class",
  "compow",
  "concat",
  "congruent",
  "congruent2",
  "conj",
  "contained",
  "conv_graph",
  "conv_rel",
  "conv_sumC",
  "converse",
  "conversep",
  "cr_int",
  "cr_integer",
  "cr_literal",
  "cr_natural",
  "ctor_cfun",
  "ctor_char",
  "ctor_ffun",
  "ctor_finite_1",
  "ctor_finite_2",
  "ctor_finite_3",
  "ctor_finite_4",
  "ctor_finite_5",
  "ctor_fold_cfun",
  "ctor_fold_char",
  "ctor_fold_ffun",
  "ctor_fold_finite_1",
  "ctor_fold_finite_2",
  "ctor_fold_finite_3",
  "ctor_fold_finite_4",
  "ctor_fold_finite_5",
  "ctor_fold_fun_box",
  "ctor_fold_lazy_sequence",
  "ctor_fold_list",
  "ctor_fold_narrowing_cons",
  "ctor_fold_narrowing_term",
  "ctor_fold_narrowing_type",
  "ctor_fold_nibble",
  "ctor_fold_num",
  "ctor_fold_option",
  "ctor_fold_pair_box",
  "ctor_fold_pred",
  "ctor_fold_property",
  "ctor_fold_seq",
  "ctor_fold_sumbool",
  "ctor_fold_term",
  "ctor_fold_three_valued",
  "ctor_fold_tuple_isomorphism",
  "ctor_fold_typerep",
  "ctor_fold_unknown",
  "ctor_fold_word",
  "ctor_fun_box",
  "ctor_lazy_sequence",
  "ctor_list",
  "ctor_narrowing_cons",
  "ctor_narrowing_term",
  "ctor_narrowing_type",
  "ctor_nibble",
  "ctor_num",
  "ctor_option",
  "ctor_pair_box",
  "ctor_pred",
  "ctor_property",
  "ctor_rec_cfun",
  "ctor_rec_char",
  "ctor_rec_ffun",
  "ctor_rec_finite_1",
  "ctor_rec_finite_2",
  "ctor_rec_finite_3",
  "ctor_rec_finite_4",
  "ctor_rec_finite_5",
  "ctor_rec_fun_box",
  "ctor_rec_lazy_sequence",
  "ctor_rec_list",
  "ctor_rec_narrowing_cons",
  "ctor_rec_narrowing_term",
  "ctor_rec_narrowing_type",
  "ctor_rec_nibble",
  "ctor_rec_num",
  "ctor_rec_option",
  "ctor_rec_pair_box",
  "ctor_rec_pred",
  "ctor_rec_property",
  "ctor_rec_seq",
  "ctor_rec_sumbool",
  "ctor_rec_term",
  "ctor_rec_three_valued",
  "ctor_rec_tuple_isomorphism",
  "ctor_rec_typerep",
  "ctor_rec_unknown",
  "ctor_rec_word",
  "ctor_seq",
  "ctor_sumbool",
  "ctor_term",
  "ctor_three_valued",
  "ctor_tuple_isomorphism",
  "ctor_typerep",
  "ctor_unknown",
  "ctor_word",
  "curr",
  "cut",
  "default",
  "default_class",
  "dense_linorder_class",
  "dense_order_class",
  "dir_image",
  "disj",
  "distinct",
  "distrib_lattice_class",
  "div",
  "div_class",
  "divide",
  "divides_aux",
  "division_ring_class",
  "divmod",
  "divmod_int",
  "divmod_int_rel",
  "divmod_integer",
  "divmod_nat",
  "divmod_nat_rel",
  "divmod_step",
  "dom",
  "drop",
  "dropWhile",
  "dtor_cfun",
  "dtor_char",
  "dtor_ffun",
  "dtor_finite_1",
  "dtor_finite_2",
  "dtor_finite_3",
  "dtor_finite_4",
  "dtor_finite_5",
  "dtor_fun_box",
  "dtor_lazy_sequence",
  "dtor_list",
  "dtor_narrowing_cons",
  "dtor_narrowing_term",
  "dtor_narrowing_type",
  "dtor_nibble",
  "dtor_num",
  "dtor_option",
  "dtor_pair_box",
  "dtor_pred",
  "dtor_property",
  "dtor_seq",
  "dtor_sumbool",
  "dtor_term",
  "dtor_three_valued",
  "dtor_tuple_isomorphism",
  "dtor_typerep",
  "dtor_unknown",
  "dtor_word",
  "dvd",
  "dvd_class",
  "embed",
  "embedS",
  "embed_list",
  "enum_class",
  "enum_the",
  "enumerate",
  "eq",
  "eq_class",
  "eq_onp",
  "equal_class",
  "equiv",
  "equivp",
  "error",
  "eventually",
  "exhaustive_class",
  "exhaustive_fun'",
  "exhaustive_fun'_graph",
  "exhaustive_fun'_rel",
  "exhaustive_fun'_sumC",
  "exhaustive_int'_graph",
  "exhaustive_int'_rel",
  "exhaustive_int'_sumC",
  "exhaustive_integer'_graph",
  "exhaustive_integer'_rel",
  "exhaustive_integer'_sumC",
  "exhaustive_natural'_graph",
  "exhaustive_natural'_rel",
  "exhaustive_natural'_sumC",
  "exhaustive_set_graph",
  "exhaustive_set_rel",
  "exhaustive_set_sumC",
  "fast_exhaustive",
  "fast_exhaustive_class",
  "fcomp",
  "field_char_0_class",
  "field_class",
  "filter",
  "filterlim",
  "filtermap",
  "finite",
  "finite_class",
  "finite_psubset",
  "flat_lub",
  "flat_ord",
  "fold",
  "fold_graph",
  "folding",
  "folding_idem",
  "folding_idem_axioms",
  "foldl",
  "foldr",
  "frequently",
  "fromCard",
  "fst",
  "fstsp",
  "full_exhaustive_class",
  "full_exhaustive_fun'",
  "full_exhaustive_fun'_graph",
  "full_exhaustive_fun'_rel",
  "full_exhaustive_fun'_sumC",
  "full_exhaustive_int'_graph",
  "full_exhaustive_int'_rel",
  "full_exhaustive_int'_sumC",
  "full_exhaustive_integer'_graph",
  "full_exhaustive_integer'_rel",
  "full_exhaustive_integer'_sumC",
  "full_exhaustive_natural'_graph",
  "full_exhaustive_natural'_rel",
  "full_exhaustive_natural'_sumC",
  "full_exhaustive_set_graph",
  "full_exhaustive_set_rel",
  "full_exhaustive_set_sumC",
  "fun_lub",
  "fun_ord",
  "fun_upd",
  "gfp",
  "greaterThan",
  "greaterThanAtMost",
  "greaterThanLessThan",
  "group_add_class",
  "hb_bind",
  "hb_flat",
  "hb_if_seq",
  "hb_map",
  "hb_not_seq",
  "hb_single",
  "hd",
  "hit_bound",
  "id",
  "idom_class",
  "image",
  "img_lub",
  "img_ord",
  "implies",
  "in_rel",
  "inf",
  "inf_class",
  "init_seg_of",
  "inj_on",
  "insert",
  "insort_insert_key",
  "insort_key",
  "int_ge_less_than",
  "int_ge_less_than2",
  "int_of_integer",
  "integer_of_int",
  "integer_of_nat",
  "integer_of_natural",
  "integer_of_num",
  "intrel",
  "inv_image",
  "inv_imagep",
  "inv_into",
  "inverse",
  "inverse_class",
  "irrefl",
  "irreflp",
  "isCardSuc",
  "is_equality",
  "is_filter",
  "is_measure",
  "is_nat",
  "is_num",
  "is_testable_class",
  "isl",
  "iso",
  "isomorphic_tuple",
  "iszero",
  "iter'_graph",
  "iter'_rel",
  "iter'_sumC",
  "iter_graph",
  "iter_rel",
  "iter_sumC",
  "iterate_graph",
  "iterate_rel",
  "iterate_sumC",
  "iteratesp",
  "last",
  "lattice_class",
  "lazy_sequence_of_list",
  "left_total",
  "left_unique",
  "lenlex",
  "less",
  "lessThan",
  "less_eq",
  "less_than",
  "lex",
  "lex_prod",
  "lexn",
  "lexord",
  "lexordp_eq",
  "lfp",
  "linear_order_on",
  "linorder_class",
  "linordered_ab_group_add_class",
  "linordered_ab_semigroup_add_class",
  "linordered_cancel_ab_semigroup_add_class",
  "linordered_comm_semiring_strict_class",
  "linordered_field_class",
  "linordered_idom_class",
  "linordered_ring_class",
  "linordered_ring_strict_class",
  "linordered_semidom_class",
  "linordered_semiring_1_class",
  "linordered_semiring_1_strict_class",
  "linordered_semiring_class",
  "linordered_semiring_strict_class",
  "list_all2",
  "list_ex",
  "list_ex1",
  "list_of_lazy_sequence",
  "list_update",
  "listprod",
  "listrel",
  "listrel1",
  "listrel1p",
  "listrelp",
  "lists",
  "listset",
  "listsp",
  "listsum",
  "log_graph",
  "log_rel",
  "log_sumC",
  "map",
  "map_add",
  "map_comp",
  "map_fun",
  "map_le",
  "map_of",
  "map_option",
  "map_pre_cfun",
  "map_pre_char",
  "map_pre_ffun",
  "map_pre_finite_1",
  "map_pre_finite_2",
  "map_pre_finite_3",
  "map_pre_finite_4",
  "map_pre_finite_5",
  "map_pre_fun_box",
  "map_pre_lazy_sequence",
  "map_pre_list",
  "map_pre_narrowing_cons",
  "map_pre_narrowing_term",
  "map_pre_narrowing_type",
  "map_pre_nibble",
  "map_pre_num",
  "map_pre_option",
  "map_pre_pair_box",
  "map_pre_pred",
  "map_pre_property",
  "map_pre_seq",
  "map_pre_sumbool",
  "map_pre_term",
  "map_pre_three_valued",
  "map_pre_tuple_isomorphism",
  "map_pre_typerep",
  "map_pre_unknown",
  "map_pre_word",
  "map_prod",
  "map_sum",
  "map_tailrec",
  "map_tailrec_rev",
  "map_tailrec_rev_graph",
  "map_tailrec_rev_rel",
  "map_tailrec_rev_sumC",
  "map_upds",
  "max",
  "max_ext",
  "max_extp",
  "max_strict",
  "max_weak",
  "measure",
  "measures",
  "member",
  "min",
  "min_ext",
  "min_strict",
  "min_weak",
  "minus",
  "minus_class",
  "mk_less",
  "mlex_prod",
  "mod",
  "mono",
  "monoid",
  "monoid_add_class",
  "monoid_axioms",
  "monoid_list",
  "monoid_mult_class",
  "monotone",
  "mult_zero_class",
  "narrowing",
  "narrowing_class",
  "narrowing_dummy_narrowing",
  "narrowing_dummy_partial_term_of",
  "nat",
  "natLeq",
  "natLess",
  "nat_gcd_graph",
  "nat_gcd_rel",
  "nat_gcd_sumC",
  "nat_list",
  "nat_of_char",
  "nat_of_integer",
  "nat_of_natural",
  "nat_of_nibble",
  "nat_of_num",
  "nat_set",
  "natural_of_integer",
  "natural_of_nat",
  "negDivAlg",
  "negDivAlg_graph",
  "negDivAlg_rel",
  "negDivAlg_sumC",
  "neg_numeral_class",
  "nibble_of_nat",
  "no_bot_class",
  "no_top_class",
  "non_empty_graph",
  "non_empty_rel",
  "non_empty_sumC",
  "norm_frac_graph",
  "norm_frac_rel",
  "norm_frac_sumC",
  "not_eq",
  "ntrancl",
  "num_class",
  "num_of_integer",
  "num_of_nat",
  "numeral",
  "numeral_class",
  "of_bool",
  "of_int",
  "of_nat",
  "ofilter",
  "ofilterIncl",
  "one_class",
  "ordIso",
  "ordLeq",
  "ordLess",
  "ord_to_filter",
  "order_bot_class",
  "order_class",
  "order_top_class",
  "ordered_ab_group_add_abs_class",
  "ordered_ab_group_add_class",
  "ordered_ab_semigroup_add_class",
  "ordered_ab_semigroup_add_imp_le_class",
  "ordered_cancel_ab_semigroup_add_class",
  "ordered_cancel_comm_monoid_diff_class",
  "ordered_cancel_comm_semiring_class",
  "ordered_cancel_semiring_class",
  "ordered_comm_monoid_add_class",
  "ordered_comm_ring_class",
  "ordered_comm_semiring_class",
  "ordered_ring_abs_class",
  "ordered_ring_class",
  "ordered_semiring_class",
  "ordering",
  "ordering_top",
  "ordering_top_axioms",
  "override_on",
  "pair_leq",
  "pair_less",
  "part_equivp",
  "partial_function_definitions",
  "partial_order_on",
  "partial_term_of",
  "partial_term_of_class",
  "partition",
  "pcr_int",
  "pcr_integer",
  "pcr_literal",
  "pcr_natural",
  "plus",
  "plus_class",
  "posDivAlg",
  "posDivAlg_graph",
  "posDivAlg_rel",
  "posDivAlg_sumC",
  "power",
  "power_class",
  "pred_fun",
  "pred_list",
  "pred_nat",
  "pred_numeral",
  "pred_of_set",
  "pred_option",
  "pred_prod",
  "pred_sum",
  "preorder_class",
  "preorder_on",
  "principal",
  "print",
  "print_class",
  "product_lists",
  "projl",
  "projr",
  "quot_type",
  "quotient",
  "ran",
  "random_aux_finite_1",
  "random_aux_finite_2",
  "random_aux_finite_3",
  "random_aux_finite_4",
  "random_aux_finite_5",
  "random_aux_list",
  "random_aux_nibble",
  "random_aux_num",
  "random_aux_option",
  "random_aux_prod",
  "random_aux_set",
  "random_aux_set_graph",
  "random_aux_set_rel",
  "random_aux_set_sumC",
  "random_aux_sum",
  "random_aux_tuple_isomorphism",
  "random_aux_unit",
  "random_class",
  "rec_cfun",
  "rec_char",
  "rec_ffun",
  "rec_finite_1",
  "rec_finite_2",
  "rec_finite_3",
  "rec_finite_4",
  "rec_finite_5",
  "rec_fun_box",
  "rec_lazy_sequence",
  "rec_list",
  "rec_narrowing_cons",
  "rec_narrowing_term",
  "rec_narrowing_type",
  "rec_natural",
  "rec_nibble",
  "rec_num",
  "rec_option",
  "rec_pair_box",
  "rec_pred",
  "rec_property",
  "rec_seq",
  "rec_set_natural",
  "rec_sumbool",
  "rec_term",
  "rec_three_valued",
  "rec_tuple_isomorphism",
  "rec_typerep",
  "rec_unknown",
  "rec_word",
  "reduction_pair",
  "refl_on",
  "reflp",
  "regularCard",
  "relChain",
  "rel_filter",
  "rel_fun",
  "rel_option",
  "rel_pre_cfun",
  "rel_pre_char",
  "rel_pre_ffun",
  "rel_pre_finite_1",
  "rel_pre_finite_2",
  "rel_pre_finite_3",
  "rel_pre_finite_4",
  "rel_pre_finite_5",
  "rel_pre_fun_box",
  "rel_pre_lazy_sequence",
  "rel_pre_list",
  "rel_pre_narrowing_cons",
  "rel_pre_narrowing_term",
  "rel_pre_narrowing_type",
  "rel_pre_nibble",
  "rel_pre_num",
  "rel_pre_option",
  "rel_pre_pair_box",
  "rel_pre_pred",
  "rel_pre_property",
  "rel_pre_seq",
  "rel_pre_sumbool",
  "rel_pre_term",
  "rel_pre_three_valued",
  "rel_pre_tuple_isomorphism",
  "rel_pre_typerep",
  "rel_pre_unknown",
  "rel_pre_word",
  "rel_pred_comp",
  "rel_prod",
  "rel_set",
  "rel_sum",
  "relcomp",
  "relcompp",
  "remdups",
  "remdups_adj",
  "remdups_adj_graph",
  "remdups_adj_rel",
  "remdups_adj_sumC",
  "remove1",
  "removeAll",
  "restrict_map",
  "return_list",
  "rev",
  "rev_implies",
  "right_total",
  "right_unique",
  "ring_1_class",
  "ring_1_no_zero_divisors_class",
  "ring_char_0_class",
  "ring_class",
  "ring_div_class",
  "ring_no_zero_divisors_class",
  "ring_parity_class",
  "rotate",
  "rotate1",
  "rp_inv_image",
  "rtrancl",
  "rtranclp",
  "same_fst",
  "scomp",
  "semidom_class",
  "semigroup",
  "semigroup_add_class",
  "semigroup_mult_class",
  "semilattice",
  "semilattice_axioms",
  "semilattice_inf_class",
  "semilattice_neutr",
  "semilattice_neutr_order",
  "semilattice_neutr_set",
  "semilattice_order",
  "semilattice_order_axioms",
  "semilattice_order_neutr_set",
  "semilattice_order_set",
  "semilattice_set",
  "semilattice_sup_class",
  "semiring_0_cancel_class",
  "semiring_0_class",
  "semiring_1_cancel_class",
  "semiring_1_class",
  "semiring_char_0_class",
  "semiring_class",
  "semiring_div_class",
  "semiring_div_parity_class",
  "semiring_no_zero_divisors_class",
  "semiring_numeral_class",
  "semiring_numeral_div_class",
  "semiring_parity_class",
  "separate",
  "set",
  "set1_pre_list",
  "set1_pre_option",
  "set2_pre_list",
  "set2_pre_option",
  "set_Cons",
  "set_of_pred",
  "set_of_seq",
  "set_option",
  "set_pre_cfun",
  "set_pre_char",
  "set_pre_ffun",
  "set_pre_finite_1",
  "set_pre_finite_2",
  "set_pre_finite_3",
  "set_pre_finite_4",
  "set_pre_finite_5",
  "set_pre_fun_box",
  "set_pre_lazy_sequence",
  "set_pre_narrowing_cons",
  "set_pre_narrowing_term",
  "set_pre_narrowing_type",
  "set_pre_nibble",
  "set_pre_num",
  "set_pre_pair_box",
  "set_pre_pred",
  "set_pre_property",
  "set_pre_seq",
  "set_pre_sumbool",
  "set_pre_term",
  "set_pre_three_valued",
  "set_pre_tuple_isomorphism",
  "set_pre_typerep",
  "set_pre_unknown",
  "set_pre_word",
  "setlp",
  "setprod",
  "setrp",
  "setsum",
  "sgn",
  "sgn_class",
  "sgn_if_class",
  "simp_implies",
  "single_valued",
  "size",
  "size_bool",
  "size_char",
  "size_class",
  "size_list",
  "size_natural",
  "size_nibble",
  "size_num",
  "size_option",
  "size_prod",
  "size_sum",
  "size_tuple_isomorphism",
  "size_typerep",
  "size_unit",
  "small_lazy",
  "small_lazy'",
  "small_lazy'_graph",
  "small_lazy'_rel",
  "small_lazy'_sumC",
  "small_lazy_class",
  "small_lazy_list_graph",
  "small_lazy_list_rel",
  "small_lazy_list_sumC",
  "snd",
  "sndsp",
  "sort_key",
  "sorted",
  "sorted_list_of_set",
  "splice",
  "splice_graph",
  "splice_rel",
  "splice_sumC",
  "strict_linear_order_on",
  "strict_mono",
  "sublist",
  "sublists",
  "sup",
  "sup_class",
  "sym",
  "symp",
  "take",
  "takeWhile",
  "term_of_class",
  "the",
  "the_default",
  "the_elem",
  "the_inv_into",
  "those",
  "times",
  "times_class",
  "tl",
  "toCard",
  "toCard_pred",
  "top",
  "top_class",
  "total_on",
  "trancl",
  "tranclp",
  "trans",
  "transfer_bforall",
  "transfer_forall",
  "transfer_implies",
  "transfer_morphism",
  "transp",
  "transpose",
  "transpose_graph",
  "transpose_rel",
  "transpose_sumC",
  "tsub",
  "type_class",
  "type_definition",
  "typerep_class",
  "typerep_of",
  "uminus",
  "uminus_class",
  "unbounded_dense_linorder_class",
  "uncurry",
  "undefined",
  "under",
  "underS",
  "univ",
  "upt",
  "upto",
  "upto_aux",
  "upto_graph",
  "upto_rel",
  "upto_sumC",
  "valterm_emptyset",
  "valtermify_insert",
  "vimage",
  "well_order_on",
  "wellorder_class",
  "wf",
  "wfP",
  "wf_wfrec'",
  "wfrec",
  "wfrec_rel",
  "wit_list",
  "wit_option",
  "wit_pre_cfun",
  "wit_pre_char",
  "wit_pre_ffun",
  "wit_pre_finite_1",
  "wit_pre_finite_2",
  "wit_pre_finite_3",
  "wit_pre_finite_4",
  "wit_pre_finite_5",
  "wit_pre_fun_box",
  "wit_pre_lazy_sequence",
  "wit_pre_list",
  "wit_pre_narrowing_cons",
  "wit_pre_narrowing_term",
  "wit_pre_narrowing_type",
  "wit_pre_nibble",
  "wit_pre_num",
  "wit_pre_option",
  "wit_pre_pair_box",
  "wit_pre_pred",
  "wit_pre_property",
  "wit_pre_seq",
  "wit_pre_sumbool",
  "wit_pre_term",
  "wit_pre_three_valued",
  "wit_pre_tuple_isomorphism",
  "wit_pre_typerep",
  "wit_pre_unknown",
  "wit_pre_word",
  "wo_rel",
  "zero_class",
  "zero_neq_one_class",
  "zip"]

used_thy_names = ["ATP",
  "Archimedean_Field",
  "BNF_Cardinal_Arithmetic",
  "BNF_Cardinal_Order_Relation",
  "BNF_Composition",
  "BNF_Def",
  "BNF_Fixpoint_Base",
  "BNF_Greatest_Fixpoint",
  "BNF_Least_Fixpoint",
  "BNF_Wellorder_Constructions",
  "BNF_Wellorder_Embedding",
  "BNF_Wellorder_Relation",
  "Basic_BNF_LFPs",
  "Basic_BNFs",
  "Binomial",
  "Code_Evaluation",
  "Code_Generator",
  "Code_Numeral",
  "Coinduction",
  "Complete_Lattices",
  "Complete_Partial_Order",
  "Complex",
  "Complex_Main",
  "Conditionally_Complete_Lattices",
  "Ctr_Sugar",
  "Deriv",
  "Divides",
  "Enum",
  "Equiv_Relations",
  "Extraction",
  "Fields",
  "Filter",
  "Finite_Set",
  "Fun",
  "Fun_Def",
  "Fun_Def_Base",
  "GCD",
  "Groebner_Basis",
  "Groups",
  "Groups_Big",
  "Groups_List",
  "HOL",
  "Hilbert_Choice",
  "Inductive",
  "Inequalities",
  "Int",
  "Lattices",
  "Lattices_Big",
  "Lazy_Sequence",
  "Lifting",
  "Lifting_Set",
  "Limited_Sequence",
  "Limits",
  "List",
  "MacLaurin",
  "Main",
  "Map",
  "Meson",
  "Metis",
  "Nat",
  "Nat_Transfer",
  "Nitpick",
  "NthRoot",
  "Num",
  "Numeral_Simprocs",
  "Option",
  "Order_Relation",
  "Orderings",
  "Parity",
  "Partial_Function",
  "Power",
  "Predicate",
  "Predicate_Compile",
  "Prelude",
  "Presburger",
  "Product_Type",
  "Pure",
  "Quickcheck_Exhaustive",
  "Quickcheck_Narrowing",
  "Quickcheck_Random",
  "Quotient",
  "Random",
  "Random_Pred",
  "Random_Sequence",
  "Rat",
  "Real",
  "Real_Vector_Spaces",
  "Record",
  "Relation",
  "Rings",
  "SAT",
  "SMT",
  "Semiring_Normalization",
  "Series",
  "Set",
  "Set_Interval",
  "Sledgehammer",
  "String",
  "Sum_Type",
  "Taylor",
  "Topological_Spaces",
  "Transcendental",
  "Transfer",
  "Transitive_Closure",
  "Typedef",
  "Typerep",
  "Wellfounded",
  "Wfrec",
  "Zorn"]
