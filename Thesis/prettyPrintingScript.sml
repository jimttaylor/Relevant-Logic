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

val _ = overload_on("Mz", “RM.RF.Z”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Mz)"],
                  term_name = "Mz", paren_style = Always}

val _ = overload_on("Mr", “λRM. RM.RF.R”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Prefix 2300, pp_elements = [TOK "(Mr)"],
                  term_name = "Mr", paren_style = OnlyIfNecessary}

val _ = overload_on("Msss", “λw. RM.RF.STAR(RM.RF.STAR(RM.RF.STAR w))”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Msss)"],
                  term_name = "Msss", paren_style = OnlyIfNecessary} 

val _ = overload_on("Mss", “λw. RM.RF.STAR(RM.RF.STAR w)”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Mss)"],
                  term_name = "Mss", paren_style = OnlyIfNecessary} 

val _ = overload_on("Ms", “λw. RM.RF.STAR w”)
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

val _ = overload_on("Fz", “RF.Z”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Fz)"],
                  term_name = "Fz", paren_style = OnlyIfNecessary}

val _ = overload_on("Fr", “λRF. RF.R”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Prefix 2300, pp_elements = [TOK "(Fr)"],
                  term_name = "Fr", paren_style = OnlyIfNecessary}

val _ = overload_on("Fsss", “λw. RF.STAR (RF.STAR (RF.STAR w))”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Fsss)"],
                  term_name = "Fsss", paren_style = OnlyIfNecessary}

val _ = overload_on("Fss", “λw. RF.STAR (RF.STAR w)”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Fss)"],
                  term_name = "Fss", paren_style = OnlyIfNecessary}

val _ = overload_on("Fs", “λw. RF.STAR w”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(Fs)"],
                  term_name = "Fs", paren_style = OnlyIfNecessary}


Overload "MHolds" = “λ RM a. Holds RM RM.RF.Z a”
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Suffix 2100,
			term_name = "MHolds",
			pp_elements = [TOK "(MHOLDS1)"]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Closefix,
			term_name = "Theta_i",
			pp_elements = [TOK "(Ti1)", TM, TOK "(Ti2)", TM, TOK "(Ti3)"]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Suffix 2100,
			term_name = "SUC",
			pp_elements = [TOK "(SUC)"]}


val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Closefix,
			term_name = "Theta",
			pp_elements = [TOK "(T1)", TM, TOK "(T2)"]}

Overload "R_set" = “{p | |- p}”

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Suffix 2100,
			term_name = "APPLYING",
			pp_elements = [TOK "(Ap1)", TM, TOK "(Ap2)"]}

Overload "sENT" = “λΓ S p. sENTAILS S Γ p”
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Suffix 2100,
			term_name = "sENT",
			pp_elements = [TOK "(sENT1)", TM, TOK "(sENT2)"]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Closefix,
			term_name = "Canonical_Frame",
			pp_elements = [TOK "(CF1)", TM, TOK "(CF2)"]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Closefix,
			term_name = "Canonical_Model",
			pp_elements = [TOK "(CM1)", TM, TOK "(CM2)"]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Prefix 2300,
			term_name = "CONJl",
			pp_elements = [TOK "(CONJl1)"]}


Overload "LEQ" = “λx RF y. RF.R RF.Z x y”
Overload "LEQ" = “λx RM y. RM.RF.R RM.RF.Z x y”
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Infix (NONASSOC, 450),
			term_name = "LEQ",
			pp_elements = [HardSpace 1, TOK "(LEQ1)", TM, TOK "(LEQ2)", BreakSpace (1,0)]}

Overload "Enum" = “λn. LINV R_gn UNIV n”
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Closefix,
			term_name = "Enum",
			pp_elements = [TOK "(Enum1)", TM, TOK "(Enum2)"]}

Overload "ss" = “λp. {p}”
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Closefix,
			term_name = "ss",
			pp_elements = [TOK "(ss1)", TM, TOK "(ss2)"]}

val _ = export_theory()
