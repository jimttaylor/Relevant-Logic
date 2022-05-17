open HolKernel boolLib Parse bossLib
open RLRulesTheory GoldblattSlaneyEquivTheory

val _ = new_theory "prettyPrintingGSE"

val _ = remove_termtok{ tok = "==>", term_name = "⇒"}
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Infixr 200,
			term_name = "==>",
			pp_elements = [HardSpace 1, TOK "⇒", BreakSpace(1,10)]}

val _ = export_theory()