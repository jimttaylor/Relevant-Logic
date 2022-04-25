open HolKernel boolLib Parse bossLib
open RMSemanticsTheory
val _ = new_theory "prettyPrinting"

val _ = remove_termtok{ tok = "==>", term_name = "⇒"}
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Infixr 200,
			term_name = "==>",
			pp_elements = [HardSpace 1, TOK "⇒", BreakSpace(1,10)]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Suffix 2100,
			term_name = "Holds",
			pp_elements = [TOK "(HOLDS1)", TM, TOK "(HOLDS2)"]}

(* Overloads for Models *)

val _ = overload_on("Mw", “λRM. RM.RF.W”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Mw)"],
                  term_name = "Mw", paren_style = OnlyIfNecessary}

val _ = overload_on("Mz", “λRM. RM.RF.Z”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Mz)"],
                  term_name = "Mz", paren_style = OnlyIfNecessary}

val _ = overload_on("Mr", “λRM. RM.RF.R”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Mr)"],
                  term_name = "Mr", paren_style = OnlyIfNecessary}

val _ = overload_on("Ms", “λRM. RM.RF.STAR”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Ms)"],
                  term_name = "Ms", paren_style = OnlyIfNecessary} 

val _ = overload_on("Mv", “λRM. RM.VF”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Mv)"],
                  term_name = "Mv", paren_style = OnlyIfNecessary}

val _ = overload_on("Mf", “λRM. RM.RF”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Mf)"],
                  term_name = "Mf", paren_style = OnlyIfNecessary}

(* Overloads for Frames *)

val _ = overload_on("Fw", “λRF. RF.W”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Fw)"],
                  term_name = "Fw", paren_style = OnlyIfNecessary}

val _ = overload_on("Fz", “λRF. RF.Z”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Fz)"],
                  term_name = "Fz", paren_style = OnlyIfNecessary}

val _ = overload_on("Fr", “λRF. RF.R”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Fr)"],
                  term_name = "Fr", paren_style = OnlyIfNecessary}

val _ = overload_on("Fs", “λRF. RF.STAR”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Fs)"],
                  term_name = "Fs", paren_style = OnlyIfNecessary}


Overload "MHolds" = “λ RM a. Holds RM RM.RF.Z a”

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Suffix 2100,
			term_name = "MHolds",
			pp_elements = [TOK "(MHOLDS1)"]}

val _ = export_theory()
