open HolKernel boolLib Parse bossLib
open CoverSemanticsTheory
val _ = new_theory "prettyPrintingCS"

val _ = remove_termtok{ tok = "==>", term_name = "⇒"}
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Infixr 200,
			term_name = "==>",
			pp_elements = [HardSpace 1, TOK "⇒", BreakSpace(1,2)]}

val _ = remove_termtok{ tok = "<=>", term_name = "⇔"}
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Infixr 200,
			term_name = "<=>",
			pp_elements = [HardSpace 1, TOK "⇔", BreakSpace(1,2)]}


val _ = remove_termtok{ tok = "=", term_name = "="}
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Infixr 200,
			term_name = "=",
			pp_elements = [HardSpace 1, TOK "=", BreakSpace(1,2)]}

(* Overloads for Models *)



val _ = export_theory()
