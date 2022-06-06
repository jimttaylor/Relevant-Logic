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


Overload "cfuse" = “λx y. CAN_FUSION x y”
Overload "corth" = “λx y. CAN_ORTH x y”

Overload "cfuse" = “λx y. op_Lift_1 CAN_FUSION x y”
Overload "cfuse" = “λx y. op_Lift_2 CAN_FUSION x y”

Overload "corth" = “λx y. rel_Lift_1 CAN_ORTH x y”
Overload "corth" = “λx y. rel_Lift_2 CAN_ORTH x y”


val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Infixr 400,
			term_name = "cfuse",
			pp_elements = [TOK "(cfuse)"]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Infixr 400,
			term_name = "corth",
			pp_elements = [TOK "(corth)"]}


val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Infixr 400,
			term_name = "Orthojoin",
			pp_elements = [TOK "(orthojoin)"]}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Closefix,
			term_name = "EQUIV_W",
			pp_elements = [TOK "(EQUIV_W1)", TM, TOK "(EQUIV_W2)"]}

Overload "Perps" = “λx. Perp x”
Overload "dPerp" = “λx. Perp (Perp x)”
Overload "tPerp" = “λx. Perp (Perp (Perp x))”

Overload "Perps" = “λx. Perp RCS x”
Overload "dPerp" = “λx. Perp RCS (Perp RCS x)”
Overload "tPerp" = “λx. Perp RCS (Perp RCS (Perp RCS x))”

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
            fixity = Suffix 2100, pp_elements = [TOK "(Perps)"],
            term_name = "Perp", paren_style = OnlyIfNecessary}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
            fixity = Suffix 2100, pp_elements = [TOK "(Perps)"],
            term_name = "Perps", paren_style = OnlyIfNecessary}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
            fixity = Suffix 2100, pp_elements = [TOK "(dPerp)"],
            term_name = "dPerp", paren_style = OnlyIfNecessary}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
            fixity = Suffix 2100, pp_elements = [TOK "(tPerp)"],
            term_name = "tPerp", paren_style = OnlyIfNecessary}

Overload "upfunc" = “λrcs x. Up (to_CS rcs) {x}”
Overload "upfunc" = “λcs x. Up cs {x}”
Overload "upfunc" = “λrcs X. Up (to_CS rcs) X”
Overload "upfunc" = “λcs X. Up cs X”

Overload "up_set" = “Upset (to_CS RCS)”
Overload "up_set" = “Upset (to_CS Canonical_System)”

Overload "Localized" = “Localized CS”
Overload "Localized" = “Localized (to_CS RCS)”
Overload "Localized" = “Localized (to_CS Canonical_System)”

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
            fixity = Prefix 2300, pp_elements = [TOK "(upfunc1)", TM, TOK "(upfunc2)"],
            term_name = "upfunc", paren_style = OnlyIfNecessary}

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Prefix 2300,
			term_name = "C_Holds",
			pp_elements = [TOK "(C_Holds1)", TM, TOK "(C_Holds2)", TM, TOK "(C_Holds3)", TM, TOK "(C_Holds4)", TM, TOK "(C_Holds5)"]}

Overload "MHolds" = “λ rcs prop m p . C_Holds rcs prop m rcs.E p”
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Prefix 2300,
			term_name = "MHolds",
			pp_elements = [TOK "(MHolds1)", TM, TOK "(MHolds2)", TM, TOK "(MHolds3)", TM, TOK "(MHolds4)"]}

Overload "nMHolds" = “λ rcs prop m p . ¬(C_Holds rcs prop m rcs.E p)”
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Prefix 2300,
			term_name = "nMHolds",
			pp_elements = [TOK "(nMHolds1)", TM, TOK "(nMHolds2)", TM, TOK "(nMHolds3)", TM, TOK "(nMHolds4)"]}


val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Suffix 2100,
			term_name = "Theory",
			pp_elements = [TOK "(theory)"]}


Overload "(RCS)" = “to_CS RCS”
Overload "(Canonical_System)" = “to_CS RCS”

Overload "n|-" = “λ p. ¬( |- p)”
Overload "n|-^" = “λ g p. ¬(g |-^ p)”

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Infixl 130,
			term_name = "n|-^",
			pp_elements = [TOK "(n|-^)"]}

Overload "nC_Holds" = “λ rcs prop m w p . ¬(C_Holds rcs prop m w p)”
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Prefix 2300,
			term_name = "nC_Holds",
			pp_elements = [TOK "(nC_Holds1)", TM, TOK "(nC_Holds2)", TM, TOK "(nC_Holds3)", TM, TOK "(nC_Holds4)", TM, TOK "(nC_Holds5)"]}

Overload "E" = “RCS.E”
Overload "E" = “Canonical_System.E”
Overload "≼ₘ" = “Canonical_System.REF”

Overload "(CSw)" = “CS.W”
Overload "(RCSw)" = “RCS.W”
Overload "(CANw)" = “Canonical_System.W”


val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Closefix,
			term_name = "EQUIV",
			pp_elements = [TOK "([)", TM, TOK "(])"]} 

(*
Overload "Mp" = “λ(p :g_prop). M p”
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
			paren_style = OnlyIfNecessary,
			fixity = Closefix,
			term_name = "Mp",
			pp_elements = [TOK "(M_fun1)", TM, TOK "(M_fun2)"]}
*)
val _ = export_theory()