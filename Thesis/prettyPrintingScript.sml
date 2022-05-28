open HolKernel boolLib Parse bossLib
open RMSemanticsTheory
val _ = new_theory "prettyPrinting"

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
                  fixity = Closefix, pp_elements = [TOK "(Fr1)", TM, TOK "(Fr2)"],
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
			fixity = Closefix,
			term_name = "Theta",
			pp_elements = [TOK "(T1)", TM, TOK "(T2)"]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Closefix,
			term_name = "B_WORLD_i",
			pp_elements = [TOK "(b1)", TM, TOK "(b2)", TM, TOK "(b3)", TM, TOK "(b3)", TM, TOK "(b4)"]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Closefix,
			term_name = "B_WORLD",
			pp_elements = [TOK "(B1)", TM , TOK "(B2)", TM , TOK "(B2)", TM , TOK "(B3)"]}


val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Closefix,
			term_name = "X_WORLD_i",
			pp_elements = [TOK "(x1)", TM, TOK "(x2)", TM, TOK "(x3)", TM, TOK "(x3)", TM, TOK "(x3)", TM, TOK "(x4)"]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Closefix,
			term_name = "X_WORLD",
			pp_elements = [TOK "(X1)", TM , TOK "(X2)", TM , TOK "(X2)", TM , TOK "(X2)", TM , TOK "(X3)"]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Closefix,
			term_name = "Y_WORLD_i",
			pp_elements = [TOK "(y1)", TM, TOK "(y2)", TM, TOK "(y3)", TM, TOK "(y3)", TM, TOK "(y4)"]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Closefix,
			term_name = "Y_WORLD",
			pp_elements = [TOK "(Y1)", TM , TOK "(Y2)", TM , TOK "(Y2)", TM , TOK "(Y3)"]}


Overload "R_set" = “{p | |- p}”

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Suffix 2100,
			term_name = "APPLYING",
			pp_elements = [TOK "(Ap1)", TM, TOK "(Ap2)"]}

Overload "sENT" = “λΓ S p. sENTAILS S Γ p”
Overload "theta_entails" =  “λt. sENTAILS t”
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Suffix 2100,
			term_name = "sENT",
			pp_elements = [TOK "(sENT1)", TM, TOK "(sENT2)"]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Closefix,
			term_name = "theta_entails",
			pp_elements = [TOK "(theta_entails1)", TM, TOK "(theta_entails2)"]}

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

Overload "s_theory1" = “λA B. S_Theory A B”
Overload "s_theory2" = “λA. S_Theory A”

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Suffix 2100,
			term_name = "s_theory1",
			pp_elements = [TOK "(s_theory1)", HardSpace 1, TM, TOK "(s_theory2)"]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Suffix 2100,
			term_name = "s_theory2",
			pp_elements = [TOK "(s_theory1)"]}

val _ = overload_on("CFsss", “λw. (Canonical_Frame p).STAR ((Canonical_Frame p).STAR ((Canonical_Frame p).STAR w))”)
val _ = overload_on("CFsss", “λw. (Canonical_Frame A).STAR ((Canonical_Frame A).STAR ((Canonical_Frame A).STAR w))”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(CFsss)"],
                  term_name = "CFsss", paren_style = OnlyIfNecessary}

val _ = overload_on("CFss", “λw. (Canonical_Frame p).STAR ((Canonical_Frame p).STAR w)”)
val _ = overload_on("CFss", “λw. (Canonical_Frame A).STAR ((Canonical_Frame A).STAR w)”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(CFss)"],
                  term_name = "CFss", paren_style = OnlyIfNecessary}

val _ = overload_on("CFs", “λw. (Canonical_Frame p).STAR w”)
val _ = overload_on("CFs", “λw. (Canonical_Frame A).STAR w”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(CFs)"],
                  term_name = "CFs", paren_style = OnlyIfNecessary}


val _ = overload_on("CMsss", “λw. (Canonical_Model p).RF.STAR((Canonical_Model p).RF.STAR((Canonical_Model p).RF.STAR w))”)
val _ = overload_on("CMsss", “λw. (Canonical_Model A).RF.STAR((Canonical_Model A).RF.STAR((Canonical_Model A).RF.STAR w))”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(CMsss)"],
                  term_name = "CMsss", paren_style = OnlyIfNecessary} 

val _ = overload_on("CMss", “λw. (Canonical_Model p).RF.STAR((Canonical_Model p).RF.STAR w)”)
val _ = overload_on("CMss", “λw. (Canonical_Model A).RF.STAR((Canonical_Model A).RF.STAR w)”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(CMss)"],
                  term_name = "CMss", paren_style = OnlyIfNecessary} 

val _ = overload_on("CMs", “λw. (Canonical_Model p).RF.STAR w”)
val _ = overload_on("CMs", “λw. (Canonical_Model A).RF.STAR w”)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Suffix 2100, pp_elements = [TOK "(CMs)"],
                  term_name = "CMs", paren_style = OnlyIfNecessary} 

Theorem B_WORLD_i_def_pp = RMSemanticsTheory.B_WORLD_i_def |> SRULE[arithmeticTheory.ADD1] 
Theorem Y_WORLD_i_def_pp = RMSemanticsTheory.Y_WORLD_i_def |> SRULE[arithmeticTheory.ADD1] 
Theorem X_WORLD_i_def_pp = RMSemanticsTheory.X_WORLD_i_def |> SRULE[arithmeticTheory.ADD1] 
Theorem Theta_i_def_pp = RMSemanticsTheory.Theta_i_def |> SRULE[arithmeticTheory.ADD1] 

val _ = export_theory()
