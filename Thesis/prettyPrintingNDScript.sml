open HolKernel boolLib Parse bossLib
open NaturalDeductionTheory

val _ = new_theory "prettyPrintingND"

val _ = remove_termtok{ tok = "==>", term_name = "⇒"}
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Infixr 200,
			term_name = "==>",
			pp_elements = [HardSpace 1, TOK "⇒", BreakSpace(1,10)]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Suffix 2100,
			term_name = "REPLACE",
			pp_elements = [TOK "(REPLACE1)", TM, TOK "(REPLACE2)"]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Closefix,
			term_name = "bg",
			pp_elements = [TOK "(bg1)", TM, TOK "(bg2)"]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Prefix 1,
			term_name = "PROP",
			pp_elements = [TOK "(PROP)"]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Prefix 1,
			term_name = "|-",
			pp_elements = [TOK "(|-)"]}


val _ = export_theory()
