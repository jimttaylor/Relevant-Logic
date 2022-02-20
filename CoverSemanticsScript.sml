
open HolKernel Parse boolLib bossLib pred_setTheory;
open relationTheory;
open GoldblattRLTheory RLRulesTheory;


val _ = new_theory "CoverSemantics";

Datatype:
  COVER_SYSTEM = <| W: α set; REF: α -> α -> bool; COVER: α set -> α -> bool |>
End

Definition Upset_def:
  Upset CS X ⇔ X ⊆ CS.W ∧ ∀d e. d ∈ X ∧ e ∈ CS.W ∧ CS.REF d e ⇒ e ∈ X  
End     

Definition Up_def:
  Up CS x = {u | u ∈ CS.W ∧ ∃w. w ∈ x ∧ CS.REF w u}
End
     
Definition Is_Cover_System_def:
  Is_Cover_System CS ⇔ PreOrder CS.REF ∧
                       (∀x y. CS.REF x y ⇒ x ∈ CS.W ∧ y ∈ CS.W) ∧
                       (∀x. x ∈ CS.W ⇒ ∃Z. CS.COVER Z x) ∧
                       (∀x Z. x ∈ CS.W ∧ CS.COVER Z x ⇒ Z ⊆ Up CS {x})
End

Theorem Upset_up:
  Is_Cover_System CS ⇒ 
  (Upset CS X ⇔ Up CS X = X)
Proof
  rw[Up_def, Upset_def, EXTENSION, EQ_IMP_THM]
  >- metis_tac[SUBSET_DEF]
  >- (qexists_tac ‘x’ >> gs[Is_Cover_System_def, PreOrder, reflexive_def])
  >- gs[SUBSET_DEF]
  >- metis_tac[Is_Cover_System_def]
QED


Theorem Upset_UNION:
  ∀CS A B. Upset CS A ∧ Upset CS B ⇒ Upset CS (A ∪ B)
Proof
  rw[Upset_def] >> metis_tac[]
QED


Theorem Upset_INTER:
  ∀CS A B. Upset CS A ∧ Upset CS B ⇒ Upset CS (A ∩ B)
Proof
  rw[Upset_def, SUBSET_DEF] >> metis_tac[]
QED

        
Definition j_def:
  j CS X = {w | w ∈ CS.W ∧ ∃Z. CS.COVER Z w ∧ Z ⊆ X}
End

Definition Localized_def:
  Localized CS X ⇔ j CS X ⊆ X
End

Theorem lemma6_3_1:
  Is_Cover_System CS ∧ Upset CS X ⇒ X ⊆ j CS X
Proof
  rw[j_def, SUBSET_DEF]
  >- gs[Upset_def, SUBSET_DEF]
  >> ‘Up CS {x} ⊆ X’ by
    (gs[Upset_def] >> rw[SUBSET_DEF, Up_def] >>
     last_x_assum irule >> simp[] >>
     metis_tac[]
    ) >> 
  gs[Is_Cover_System_def] >>
  qpat_x_assum ‘∀x. x ∈ CS.W ⇒ ∃Z. CS.COVER Z x’ $ qspec_then ‘x’ strip_assume_tac >>
  gs[Upset_def, SUBSET_DEF] >> qexists_tac ‘Z’ >> simp[] >> 
  last_x_assum $ qspecl_then [‘x’, ‘Z’] strip_assume_tac >> gs[]
QED

Datatype:
  R_COVER_SYSTEM = <| W: α set; REF: α -> α -> bool; COVER: α set -> α -> bool; FUSE: α -> α -> α; E: α; ORTH: α -> α -> bool |>
End

Definition rel_Lift_1:
   rel_Lift_1 R X y ⇔ ∀x. x ∈ X ⇒ R x y 
End

Definition rel_Lift_2:
   rel_Lift_2 R x Y ⇔ ∀y. y ∈ Y ⇒ R x y 
End


Definition op_Lift_1:
   op_Lift_1 R X y = {R x y | x ∈ X} 
End

Definition op_Lift_2:
   op_Lift_2 R x Y = {R x y | y ∈ Y} 
End        

Definition to_CS_def:
  (to_CS: α R_COVER_SYSTEM -> α COVER_SYSTEM) RCS = <|W := RCS.W; REF := RCS.REF; COVER := RCS.COVER |>
End
           
val _= set_mapped_fixity {term_name = "BOT", fixity = Infix (NONASSOC, 450), tok="⊥"};
Overload "BOT" = “λ x y. RCS.ORTH (x: α) y”
Overload "BOT" = “λ x y. rel_Lift_1 RCS.ORTH (x: α set) y”
Overload "BOT" = “λ x y. rel_Lift_2 RCS.ORTH (x: α) y”

val _= set_mapped_fixity {term_name = "FUSE", fixity = Infix (NONASSOC, 450), tok="⬝"};
Overload "FUSE" = “λ x y. RCS.FUSE (x: α) y”
Overload "FUSE" = “λ x y. op_Lift_1 RCS.FUSE (x: α set) y”
Overload "FUSE" = “λ x y. op_Lift_2 RCS.FUSE (x: α) y”

val _= set_mapped_fixity {term_name = "REF", fixity = Infix (NONASSOC, 450), tok="≼"};
Overload "REF" = “λ x y. RCS.REF (x: α) y”


val _= set_mapped_fixity {term_name = "COVER", fixity = Infix (NONASSOC, 450), tok="▹"};
Overload "COVER" = “λ (x : α set) y. RCS.COVER x y”
                     
         
Overload "j" = “λ (X: α set). j (to_CS RCS) X”
Overload "Upset" = “λ (X: α set). Upset (to_CS RCS) X”
Overload "Localized" = “λ (X: α set). Localized (to_CS RCS) X”


Definition Is_Relevant_Cover_System_def:
  Is_Relevant_Cover_System RCS ⇔
    RCS.E ∈ RCS.W ∧
    (∀x y. x ≼ y ⇒ x ∈ RCS.W ∧ y ∈ RCS.W) ∧
    (∀x Z. Z ▹ x ⇒ x ∈ RCS.W ∧ Z ⊆ RCS.W) ∧
    (∀x y. x ∈ RCS.W ∧ y ∈ RCS.W ⇒ x ⬝ y ∈ RCS.W) ∧
    (∀x y. x ⊥ y ⇒ x ∈ RCS.W ∧ y ∈ RCS.W) ∧
    Is_Cover_System (to_CS RCS) ∧

    (* SQUARE-DECREASING COMMUNITIVE ORDERED MONOID *)
    (∀x. x ∈ RCS.W ⇒ (x ⬝ RCS.E) = x) ∧
    (∀x. x ∈ RCS.W ⇒ (RCS.E ⬝ x) = x) ∧
    (∀x y. x ∈ RCS.W ∧ y ∈ RCS.W ⇒ (x ⬝ y) = (y ⬝ x)) ∧
    (∀x y z. x ∈ RCS.W ∧ y ∈ RCS.W ∧ z ∈ RCS.W ⇒ (x ⬝ (y ⬝ z)) = ((x ⬝ y) ⬝ z)) ∧
    (∀x x' y y'. x ≼ x' ∧ y ≼ y' ⇒ (x ⬝ y) ≼ (x' ⬝ y')) ∧
    (∀x. x ∈ RCS.W ⇒ (x ⬝ x) ≼ x) ∧
        
    (* OTHER *)
    (∀x y Z. Z ▹ x ⇒ (Z ⬝ y) ▹ (x ⬝ y)) ∧
    (∀x x' y y'. x ≼ x' ∧ y ≼ y' ∧ x ⊥ y ⇒ x' ⊥ y') ∧
    (∀x Z. Z ▹ x ∧ Z ⊥ RCS.E ⇒ x ⊥ RCS.E) ∧ 
    (∀x y z. x ∈ RCS.W ∧ y ∈ RCS.W ∧ z ∈ RCS.W ∧ (x ⬝ y) ⊥ z ⇒ (x ⬝ z) ⊥ y)
End
        
Theorem RCS_IDENTITY               = Is_Relevant_Cover_System_def |> iffLR |> cj 1
Theorem RCS_REFINEMENT_CLOSURE     = Is_Relevant_Cover_System_def |> iffLR |> cj 2
Theorem RCS_COVER_CLOSURE          = Is_Relevant_Cover_System_def |> iffLR |> cj 3
Theorem RCS_FUSION_CLOSURE         = Is_Relevant_Cover_System_def |> iffLR |> cj 4
Theorem RCS_ORTHOGONAL_CLOSURE     = Is_Relevant_Cover_System_def |> iffLR |> cj 5
Theorem RCS_COVER_SYSTEM           = Is_Relevant_Cover_System_def |> iffLR |> cj 6

Theorem RCS_FUSION_RIGHT_IDENTITY  = Is_Relevant_Cover_System_def |> iffLR |> cj 7
Theorem RCS_FUSION_LEFT_IDENTITY   = Is_Relevant_Cover_System_def |> iffLR |> cj 8
Theorem RCS_FUSION_COMM            = Is_Relevant_Cover_System_def |> iffLR |> cj 9
Theorem RCS_FUSION_ASSOC_LR        = Is_Relevant_Cover_System_def |> iffLR |> cj 10
Theorem RCS_FUSION_MONO_REFINEMENT = Is_Relevant_Cover_System_def |> iffLR |> cj 11
Theorem RCS_FUSION_SQUARE_DECREASE = Is_Relevant_Cover_System_def |> iffLR |> cj 12

Theorem RCS_FUSION_COVERING        = Is_Relevant_Cover_System_def |> iffLR |> cj 13
Theorem RCS_REFINEMENT_ORTHOGONAL  = Is_Relevant_Cover_System_def |> iffLR |> cj 14
Theorem RCS_IDENTITY_ORTH_IS_LOCAL = Is_Relevant_Cover_System_def |> iffLR |> cj 15
Theorem RCS_CONTRAPOSITION         = Is_Relevant_Cover_System_def |> iffLR |> cj 16

Theorem RCS_PREORDER:
  Is_Relevant_Cover_System RCS ⇒
  PreOrder RCS.REF
Proof
  rw[] >> drule RCS_COVER_SYSTEM >> simp[to_CS_def] >> 
  rw[Is_Cover_System_def]
QED
        
Definition Perp_def:
  Perp RCS X = {y | y ∈ RCS.W ∧ ∀x. x ∈ X ⇒ RCS.ORTH y x}
End

Overload "Perp" = “λ (X: α set). Perp RCS X”


Theorem to_CS_IS_COVER:
  ∀RCS. Is_Relevant_Cover_System RCS ⇒
        Is_Cover_System (to_CS RCS)
Proof
  rw[to_CS_def, RCS_COVER_SYSTEM]
QED

Definition Is_Prop_def:
  Is_Prop RCS X ⇔ (Localized (to_CS RCS) X ∧ Upset (to_CS RCS) X)
End

Definition IMP_def:
  IMP RCS X Y = {w | w ∈ RCS.W ∧ {RCS.FUSE w x | x ∈ X} ⊆ Y}
End

val _= set_mapped_fixity {term_name = "IMPP", fixity = Infix (NONASSOC, 450), tok="⟹"};
Overload "IMPP" = “λ (x : α set) y. IMP RCS x y”
        
Theorem lemma6_4_1_1:
  ∀RCS x y. Is_Relevant_Cover_System RCS ∧ x ∈ RCS.W ∧ y ∈ RCS.W ⇒
            (RCS.ORTH x y ⇔ RCS.ORTH (RCS.FUSE x y) RCS.E)
Proof
  rw[EQ_IMP_THM]
  >- (irule RCS_CONTRAPOSITION >> simp[RCS_IDENTITY] >>
      metis_tac[RCS_FUSION_RIGHT_IDENTITY]
     )
  >- (drule_then strip_assume_tac RCS_CONTRAPOSITION >>
      pop_assum $ qspecl_then [‘x’, ‘y’, ‘RCS.E’]  strip_assume_tac >>
      metis_tac[RCS_FUSION_RIGHT_IDENTITY, RCS_IDENTITY]
     )
QED
        
Theorem lemma6_4_1_2:
  ∀RCS X. Is_Relevant_Cover_System RCS ∧ X ⊆ RCS.W ⇒
          Is_Prop RCS (Perp X)
Proof
  reverse $ rw[Is_Prop_def, Localized_def, Perp_def] 
  >- (rw[Upset_def, SUBSET_DEF, to_CS_def] >> irule RCS_REFINEMENT_ORTHOGONAL >>
      simp[] >> qexistsl_tac [‘d’, ‘x’] >> simp[] >>
      metis_tac[PreOrder, RCS_PREORDER, reflexive_def]
     )
  >- (rw[j_def, Once SUBSET_DEF, to_CS_def] >> rename[‘x ⊥ y’] >>
      irule (iffRL lemma6_4_1_1) >> rw[]
      >- gs[SUBSET_DEF]
      >> ‘∀z. z ∈ Z ⇒ z ⊥ y’ by gs[SUBSET_DEF] >> 
      ‘∀z. z ∈ Z ⇒ (z ⬝ y) ⊥ RCS.E’ by
        (rw[] >> irule (iffLR lemma6_4_1_1) >>
         gs[SUBSET_DEF]) >>
      drule_then strip_assume_tac RCS_FUSION_COVERING >> 
      pop_assum $ qspecl_then [‘x’, ‘y’, ‘Z’] strip_assume_tac >>
      gs[] >> irule RCS_IDENTITY_ORTH_IS_LOCAL >> simp[] >> 
      qexists_tac ‘Z ⬝ y’ >> rw[op_Lift_1, rel_Lift_1] >>
      gs[SUBSET_DEF])
QED   
        
Theorem lemma6_4_1_3:
  ∀RCS X Y. Is_Relevant_Cover_System RCS ∧ X ⊆ RCS.W ∧
            Y ⊆ RCS.W ∧ Upset Y ⇒
            Upset (X ⟹ Y)
Proof
  rw[Upset_def, to_CS_def]
  >- simp[IMP_def, Once SUBSET_DEF]
  >- (rw[IMP_def, SUBSET_DEF] >> rename [‘x ∈ X’, ‘d ∈ X ⟹ Y’] >>
      last_x_assum irule >> rw[]
      >- gs[SUBSET_DEF, RCS_REFINEMENT_CLOSURE, RCS_FUSION_CLOSURE]
      >- (qexists_tac ‘RCS.FUSE d x’ >> rw[]
          >- (gs[IMP_def, SUBSET_DEF] >> metis_tac[])
          >- (irule RCS_FUSION_MONO_REFINEMENT >>
              simp[] >> metis_tac[PreOrder, RCS_PREORDER, reflexive_def]
             )
         )
     )
QED

Theorem lemma6_4_1_4:
  ∀RCS X Y. Is_Relevant_Cover_System RCS ∧ X ⊆ RCS.W ∧
            Y ⊆ RCS.W ∧ Localized Y ⇒
            Localized (X ⟹ Y)
Proof
  rw[SUBSET_DEF, Localized_def, IMP_def, j_def, to_CS_def] >>
  rename[‘x ⬝ y ∈ Y’] >> first_x_assum irule >>
  simp[RCS_FUSION_CLOSURE] >> qexists_tac ‘Z ⬝ y’ >>
  rw[RCS_FUSION_COVERING, op_Lift_1] >> 
  metis_tac[]
QED

Theorem lemma6_4_1_5:
  ∀RCS (x: α) X. Is_Relevant_Cover_System RCS ∧ x ∈ RCS.W ∧ X ⊆ RCS.W ∧
                 x ⊥ X ⇒
                 x ⊥ j X
Proof
  rw[j_def, rel_Lift_2, to_CS_def] >> irule (iffRL lemma6_4_1_1) >> simp[] >>
  irule RCS_IDENTITY_ORTH_IS_LOCAL >> simp[] >>
  qexists_tac ‘Z ⬝ x’ >> rw[]
  >- metis_tac[RCS_FUSION_COVERING, RCS_FUSION_COMM]
  >- (pop_assum mp_tac >> rw[SUBSET_DEF, op_Lift_1, rel_Lift_1] >>
      metis_tac[lemma6_4_1_1, RCS_FUSION_COMM, SUBSET_DEF]
     )
QED
 
Theorem lemma6_4_1_5_alt:
  ∀RCS (x: α) X. Is_Relevant_Cover_System RCS ∧ X ⊆ RCS.W ⇒
                 Perp X ⊆ Perp (j X) 
Proof
  rw[SUBSET_DEF, Perp_def] >> rename[‘x ⊥ y’] >>
  assume_tac lemma6_4_1_5 >> gs[rel_Lift_2] >> first_x_assum irule >>
  simp[] >> qexists_tac ‘X’ >> gs[SUBSET_DEF]
QED

Theorem lemma6_4_1_6:
  ∀RCS X. Is_Relevant_Cover_System RCS ∧ X ⊆ RCS.W ⇒
          j X ⊆ Perp (Perp (j X)) ∧ Perp (Perp (j X)) ⊆ Perp (Perp X) 
Proof
  rw[]
  >- (rw[SUBSET_DEF, j_def, to_CS_def, Perp_def] >>
      rename [‘x ⊥ y’] >>
      ‘y ⊥ x’ suffices_by
        metis_tac[lemma6_4_1_1, RCS_FUSION_COMM] >>
      last_x_assum irule >> metis_tac[]
     ) 
  >- (‘Perp X ⊆ Perp (j X)’ suffices_by 
        rw[Perp_def, SUBSET_DEF] >>
      rw[Perp_def, SUBSET_DEF] >>
      rename [‘x ⊥ y’] >>
      assume_tac lemma6_4_1_5 >>
      pop_assum $ qspecl_then [‘RCS’, ‘x’, ‘X’] strip_assume_tac >>
      gs[rel_Lift_2]
     )
QED
        
Theorem lemma6_4_1_7:
  ∀(RCS : α R_COVER_SYSTEM) X x. Is_Relevant_Cover_System RCS ∧ Upset X ∧ X ⊆ RCS.W ∧ x ∈ RCS.W ⇒
            (x ⊥ X ⇔ x ⊥ j X)
Proof
  rw[] >>
  EQ_TAC >> strip_tac
  >- gs[lemma6_4_1_5]
  >- (gs[rel_Lift_2] >> rw[] >>
      metis_tac[lemma6_3_1, RCS_COVER_SYSTEM, SUBSET_DEF])
QED

Theorem lemma6_4_1_7_alt:
  ∀RCS (x: α) X. Is_Relevant_Cover_System RCS ∧ X ⊆ RCS.W ∧ Upset X ⇒
                 Perp X = Perp (j X)
Proof
  rw[Perp_def, EXTENSION] >> metis_tac[lemma6_4_1_7, rel_Lift_2]
QED

Theorem lemma6_4_1_8:
  ∀RCS (x: α) X. Is_Relevant_Cover_System RCS ∧ X ⊆ RCS.W ∧ Upset X ⇒
                 X ⊆ j X ∧ j X ⊆ Perp (Perp (j X)) ∧ Perp (Perp (j X)) = Perp (Perp X)
Proof
  rw[lemma6_4_1_7_alt, lemma6_4_1_6, lemma6_3_1, RCS_COVER_SYSTEM]  
QED

Theorem corollary6_4_2:
  ∀RCS (X: α set). Is_Relevant_Cover_System RCS ∧ X ⊆ RCS.W ∧ Upset X ∧ X = Perp (Perp X) ⇒ 
                   Is_Prop RCS X 
Proof
  rw[Is_Prop_def, Localized_def] >>
  metis_tac[SUBSET_DEF, lemma6_4_1_8]
QED
        
Definition Orthojoin_def:
  Orthojoin RCS X Y = Perp RCS (Perp RCS (X ∪ Y))
End
        
Overload "Orthojoin" = “λ (X: α set). Orthojoin RCS X”
        
Definition R_MODEL_SYSTEM_def:
  R_MODEL_SYSTEM RCS Ps ⇔ Is_Relevant_Cover_System RCS ∧
                          ({w | RCS.E ≼ w ∧ w ∈ RCS.W} ∈ Ps) ∧
                          (∀X. X ∈ Ps ⇒ Upset X) ∧
                          (∀X. X ∈ Ps ⇒ X = Perp (Perp X)) ∧ 
                          (∀X. X ∈ Ps ⇒ Perp X ∈ Ps) ∧
                          (∀X Y. X ∈ Ps ∧ Y ∈ Ps ⇒ X ∩ Y ∈ Ps) ∧
                          (∀X Y. X ∈ Ps ∧ Y ∈ Ps ⇒ X ⟹ Y ∈ Ps) ∧
                          (∀X Y. X ∈ Ps ∧ Y ∈ Ps ⇒ Orthojoin X Y = j (X ∪ Y))
End
        
Theorem R_MODEL_SYSTEM_R_COVER_SYSTEM    = R_MODEL_SYSTEM_def |> iffLR |> cj 1
Theorem R_MODEL_SYSTEM_E_CONE_PS         = R_MODEL_SYSTEM_def |> iffLR |> cj 2
Theorem R_MODEL_SYSTEM_PS_UPSET          = R_MODEL_SYSTEM_def |> iffLR |> cj 3
Theorem R_MODEL_SYSTEM_PS_ORTHOCLOSED    = R_MODEL_SYSTEM_def |> iffLR |> cj 4
Theorem R_MODEL_SYSTEM_PERP_PS           = R_MODEL_SYSTEM_def |> iffLR |> cj 5
Theorem R_MODEL_SYSTEM_INTER_PS          = R_MODEL_SYSTEM_def |> iffLR |> cj 6
Theorem R_MODEL_SYSTEM_IMP_PS            = R_MODEL_SYSTEM_def |> iffLR |> cj 7
Theorem R_MODEL_SYSTEM_ORTHOJOIN_J_UNION = R_MODEL_SYSTEM_def |> iffLR |> cj 8

Theorem Ps_membership:
  ∀RCS Ps X. R_MODEL_SYSTEM RCS Ps ∧ X ∈ Ps ⇒
             X ⊆ RCS.W
Proof
  rw[SUBSET_DEF] >> 
  ‘Upset X’ by metis_tac[R_MODEL_SYSTEM_PS_UPSET] >>
  gs[Upset_def] >> gs[SUBSET_DEF, to_CS_def]
QED

(*     
val _= set_mapped_fixity {term_name = "BOT", fixity = Infix (NONASSOC, 450), tok="⊥"};
Overload "BOT" = “λ x y. RCS.ORTH (x: α) y”
Overload "BOT" = “λ x y. rel_Lift_1 RCS.ORTH (x: α set) y”
Overload "BOT" = “λ x y. rel_Lift_2 RCS.ORTH (x: α) y”

val _= set_mapped_fixity {term_name = "FUSE", fixity = Infix (NONASSOC, 450), tok="⬝"};
Overload "FUSE" = “λ x y. RCS.FUSE (x: α) y”
Overload "FUSE" = “λ x y. op_Lift_1 RCS.FUSE (x: α set) y”
Overload "FUSE" = “λ x y. op_Lift_2 RCS.FUSE (x: α) y”

val _= set_mapped_fixity {term_name = "REF", fixity = Infix (NONASSOC, 450), tok="≼"};
Overload "REF" = “λ x y. RCS.REF (x: α) y”


val _= set_mapped_fixity {term_name = "COVER", fixity = Infix (NONASSOC, 450), tok="▹"};
Overload "COVER" = “λ (x : α set) y. RCS.COVER x y”
                     
         
Overload "j" = “λ (X: α set). j (to_CS RCS) X”
Overload "Upset" = “λ (X: α set). Upset (to_CS RCS) X”
Overload "Localized" = “λ (X: α set). Localized (to_CS RCS) X”
Overload "Perp" = “λ (X: α set). Perp RCS X”


val _= set_mapped_fixity {term_name = "IMPP", fixity = Infix (NONASSOC, 450), tok="⟹"};
Overload "IMPP" = “λ (x : α set) y. IMP RCS x y” 

Overload "Orthojoin" = “λ (X: α set). Orthojoin RCS X”
*)

Overload "BOT" = “λ x y. RCS.ORTH (x: g_prop set) y”
Overload "BOT" = “λ x y. rel_Lift_1 RCS.ORTH (x: (g_prop set) set) y”
Overload "BOT" = “λ x y. rel_Lift_2 RCS.ORTH (x: g_prop set) y”

Overload "FUSE" = “λ x y. RCS.FUSE (x: g_prop set) y”
Overload "FUSE" = “λ x y. op_Lift_1 RCS.FUSE (x: (g_prop set) set) y”
Overload "FUSE" = “λ x y. op_Lift_2 RCS.FUSE (x: g_prop set) y”

Overload "REF" = “λ x y. RCS.REF (x: g_prop set) y”

Overload "COVER" = “λ (x : (g_prop set) set) y. RCS.COVER x y”
                     
         
Overload "j" = “λ (X: (g_prop set) set). j (to_CS RCS) X”
Overload "Upset" = “λ (X: (g_prop set) set). Upset (to_CS RCS) X”
Overload "Localized" = “λ (X: (g_prop set) set). Localized (to_CS RCS) X”
Overload "Perp" = “λ (X: (g_prop set) set). Perp RCS X”
Overload "IMPP" = “λ (x : (g_prop set) set) y. IMP RCS x y” 
Overload "Orthojoin" = “λ (X: (g_prop set) set). Orthojoin RCS X”
        
Definition Model_Function_def:
  Model_Function (RCS: (g_prop set) R_COVER_SYSTEM) Ps M ⇔ 
    (∀a A. M (g_VAR a) = A ⇔ A ∈ Ps) ∧ 
    (M τ = {w | RCS.E ≼ w ∧ w ∈ RCS.W}) ∧
    (∀A B. M (A & B) = M A ∩ M B) ∧
    (∀A B. M (A --> B) = (M A ⟹ M B)) ∧
    (∀A. M (~A) = Perp (M A))
End

Theorem Model_Function_var = Model_Function_def |> iffLR |> cj 1
Theorem Model_Function_t   = Model_Function_def |> iffLR |> cj 2
Theorem Model_Function_and = Model_Function_def |> iffLR |> cj 3
Theorem Model_Function_imp = Model_Function_def |> iffLR |> cj 4
Theorem Model_Function_not = Model_Function_def |> iffLR |> cj 5
        
Theorem M_SUBSET_RCS_W:
  ∀RCS Ps M A. Model_Function RCS Ps M ∧ R_MODEL_SYSTEM RCS Ps ⇒ 
          M A ⊆ RCS.W
Proof
  rpt strip_tac >> Induct_on ‘A’ >> gs[Model_Function_def, SUBSET_DEF] >> rw[]
  >- metis_tac[Ps_membership, SUBSET_DEF]
  >- gs[IMP_def]
  >- gs[Perp_def]
QED

Theorem M_IN_Ps_W:
  ∀RCS Ps M A. Model_Function RCS Ps M ∧ R_MODEL_SYSTEM RCS Ps ⇒ 
          M A ∈ Ps
Proof
  rpt strip_tac >> Induct_on ‘A’ >> gs[Model_Function_def, SUBSET_DEF] >> rw[] >> 
  metis_tac[Ps_membership, SUBSET_DEF, R_MODEL_SYSTEM_IMP_PS, R_MODEL_SYSTEM_INTER_PS,
            R_MODEL_SYSTEM_PERP_PS, R_MODEL_SYSTEM_E_CONE_PS]
QED

Theorem Model_Function_or:
  ∀RCS Ps M. Model_Function RCS Ps M ⇒
             ∀A B. M(A V B) = Orthojoin (M A) (M B)
Proof
  rw[Orthojoin_def, g_OR_def] >>
  drule_then strip_assume_tac Model_Function_and >>
  drule_then strip_assume_tac Model_Function_not >> gs[] >>
  ‘Perp (M A) ∩ Perp (M B) = Perp (M A ∪ M B)’ suffices_by metis_tac[] >>
  rw[EXTENSION, Perp_def, EQ_IMP_THM] >> metis_tac[]
QED 
                                                                    
Definition C_Holds_def:
  C_Holds RCS Ps M w A ⇔ w ∈ M A ∧ Model_Function RCS Ps M
End
        
Theorem C_Holds_conditions:
  ∀RCS Ps M w. R_MODEL_SYSTEM RCS Ps ∧ Model_Function RCS Ps M ∧ w ∈ RCS.W ⇒ 
             (∀s. C_Holds RCS Ps M w (g_VAR s) ⇔ w ∈ M (g_VAR s)) ∧
             (C_Holds RCS Ps M w τ ⇔ RCS.E ≼ w) ∧
             (∀A. C_Holds RCS Ps M w (~A) ⇔ ∀u. C_Holds RCS Ps M u A ⇒ w ⊥ u) ∧
             (∀A B. C_Holds RCS Ps M w (A & B) ⇔ C_Holds RCS Ps M w A ∧ C_Holds RCS Ps M w B) ∧
             (∀A B. C_Holds RCS Ps M w (A --> B) ⇔ ∀u. C_Holds RCS Ps M u A ⇒ C_Holds RCS Ps M (w ⬝ u) B)
Proof
  rw[C_Holds_def, SUBSET_DEF, EQ_IMP_THM] >>
  gs[Model_Function_def, Perp_def, IMP_def, SUBSET_DEF] >> 
  metis_tac[RCS_ORTHOGONAL_CLOSURE, RCS_FUSION_CLOSURE, M_SUBSET_RCS_W, SUBSET_DEF]  
QED
        
Theorem Semantic_Entailment:
  ∀ RCS Ps M A B. R_MODEL_SYSTEM RCS Ps ∧ Model_Function RCS Ps M ⇒ 
        (C_Holds RCS Ps M RCS.E (A --> B) ⇔ M A ⊆ M B)
Proof
  rw[EQ_IMP_THM, C_Holds_def]
  >- (drule Model_Function_imp >> rw[SUBSET_DEF, IMP_def] >>
      gs[] >> last_x_assum irule >>
      qexists_tac ‘x’ >> simp[] >>
      irule (GSYM RCS_FUSION_LEFT_IDENTITY) >> 
      metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, M_SUBSET_RCS_W, SUBSET_DEF, Model_Function_def]
     )
  >- (drule Model_Function_imp >> rw[SUBSET_DEF, IMP_def]
      >- metis_tac[RCS_IDENTITY, R_MODEL_SYSTEM_R_COVER_SYSTEM]
      >- (‘(RCS.E ⬝ x') = x'’ suffices_by metis_tac[SUBSET_DEF] >>
          metis_tac[RCS_FUSION_LEFT_IDENTITY, R_MODEL_SYSTEM_R_COVER_SYSTEM, M_SUBSET_RCS_W, SUBSET_DEF])
     )
QED

Theorem C_Holds_at_E:
  ∀RCS Ps M A. R_MODEL_SYSTEM RCS Ps ∧ Model_Function RCS Ps M ⇒
             (C_Holds RCS Ps M RCS.E A ⇔ RCS.E ∈ M A)
Proof
  rw[C_Holds_def]
QED

Theorem E_x_is_x:
  ∀RCS Ps M x. R_MODEL_SYSTEM RCS Ps ∧ Model_Function RCS Ps M ∧ x ∈ RCS.W ⇒
               (RCS.E ⬝ x) = x
Proof
  metis_tac[M_SUBSET_RCS_W, SUBSET_DEF, R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_FUSION_LEFT_IDENTITY]
QED

Theorem soundness:
  ∀p RCS Ps M. |- p ∧ R_MODEL_SYSTEM RCS Ps ∧ Model_Function RCS Ps M ⇒ C_Holds RCS Ps M RCS.E p
Proof
  Induct_on ‘goldblatt_provable’ >> 
  rw[] >> irule (iffRL C_Holds_at_E) >> simp[]
  >- (drule Model_Function_imp >> rw[IMP_def]
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rw[SUBSET_DEF] >> metis_tac[M_SUBSET_RCS_W, E_x_is_x, SUBSET_DEF])
     )
  >- (drule_then strip_assume_tac Model_Function_imp >> 
      rw[IMP_def, SUBSET_DEF] 
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename [‘RCS.E ⬝ x ∈ RCS.W’] >> 
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >>
          gs[])
      >- (rename[‘(RCS.E ⬝ x) ⬝ y ∈ RCS.W’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >>
          gs[] >> metis_tac[M_SUBSET_RCS_W, SUBSET_DEF, RCS_FUSION_CLOSURE, R_MODEL_SYSTEM_R_COVER_SYSTEM]
         )
      >- (rename[‘((RCS.E ⬝ x) ⬝ y) ⬝ z ∈ M C’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >>
          last_x_assum irule >>
          qexists_tac ‘(x ⬝ z)’ >> rw[]
          >- (‘((y ⬝ x) ⬝ z) = (y ⬝ (x ⬝ z))’ suffices_by
                metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_FUSION_COMM, RCS_FUSION_ASSOC_LR] >>
              ‘z ∈ RCS.W’ by metis_tac[M_SUBSET_RCS_W, SUBSET_DEF] >> 
              irule (GSYM RCS_FUSION_ASSOC_LR) >> metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM])
          >- metis_tac[]
         )
     )
  >- (drule_then strip_assume_tac Model_Function_imp >> 
      rw[IMP_def, SUBSET_DEF] 
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename [‘RCS.E ⬝ x ∈ RCS.W’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x, M_SUBSET_RCS_W, SUBSET_DEF] >>
          gs[] >> metis_tac[M_SUBSET_RCS_W, SUBSET_DEF]
         )
      >- (rename[‘(RCS.E ⬝ x) ⬝ y ∈ M B’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x, M_SUBSET_RCS_W, SUBSET_DEF] >> 
          gs[] >> last_x_assum irule >> qexists_tac ‘x’ >> simp[] >> 
          metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_FUSION_COMM, M_SUBSET_RCS_W, SUBSET_DEF])
     )
  >- (drule_then strip_assume_tac Model_Function_imp >> 
      rw[IMP_def, SUBSET_DEF] 
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename[‘RCS.E ⬝ x ∈ RCS.W’] >> 
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >> 
          gs[])
      >- (rename[‘(RCS.E ⬝ x) ⬝ y ∈ M B’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >> 
          gs[] >>
          ‘Upset (M B)’ by
            metis_tac[R_MODEL_SYSTEM_PS_UPSET, M_IN_Ps_W] >>
          gs[Upset_def] >> pop_assum irule >> rw[] 
          >- (‘x ⬝ y ∈ RCS.W’ suffices_by rw[to_CS_def] >>
              metis_tac[M_SUBSET_RCS_W, SUBSET_DEF, RCS_FUSION_CLOSURE])
          >- (qexists_tac ‘(x ⬝ y) ⬝ y’ >> reverse $ rw[]
              >- (‘((x ⬝ y) ⬝ y) ≼ (x ⬝ y)’ suffices_by rw[to_CS_def] >>
                  ‘((x ⬝ y) ⬝ y) = (x ⬝ (y ⬝ y))’ by
                    (irule (GSYM RCS_FUSION_ASSOC_LR) >>
                     metis_tac [M_SUBSET_RCS_W, SUBSET_DEF, R_MODEL_SYSTEM_R_COVER_SYSTEM]) >> 
                  gs[] >> irule RCS_FUSION_MONO_REFINEMENT >> rw[] >> 
                  metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_FUSION_SQUARE_DECREASE,
                            M_SUBSET_RCS_W, SUBSET_DEF, RCS_PREORDER, PreOrder, reflexive_def])
              >- (last_x_assum $ qspec_then ‘x ⬝ y’ strip_assume_tac >>
                  ‘∀x'. (∃x''. x' = ((x ⬝ y) ⬝ x'') ∧ x'' ∈ M A) ⇒ x' ∈ M B’ by metis_tac[] >>
                  last_x_assum irule >> metis_tac[]
                 )
             )
         )
     )
  >- (drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_and >> 
      rw[IMP_def, SUBSET_DEF] 
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename[‘(RCS.E ⬝ x) ∈ M A’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x, M_SUBSET_RCS_W, SUBSET_DEF] >> 
          gs[])
     )  
  >- (drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_and >> 
      rw[IMP_def, SUBSET_DEF] 
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename[‘(RCS.E ⬝ x) ∈ M B’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x, M_SUBSET_RCS_W, SUBSET_DEF] >> 
          gs[])
     )
  >- (drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_and >> 
      rw[IMP_def, SUBSET_DEF] 
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename[‘(RCS.E ⬝ x) ∈ RCS.W’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >> 
          gs[])
      >- (rename[‘(RCS.E ⬝ x) ⬝ y ∈ M B’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >> 
          gs[] >> metis_tac[]
         )
      >- (rename[‘(RCS.E ⬝ x) ⬝ y ∈ M C’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >> 
          gs[] >> metis_tac[]
         )
     )
  >- (drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_or >> 
      rw[IMP_def, SUBSET_DEF] 
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename[‘(RCS.E ⬝ x) ∈ Orthojoin (M A) (M B)’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x, M_SUBSET_RCS_W, SUBSET_DEF] >> 
          ‘Orthojoin (M A) (M B) = j (M A ∪ M B)’ by metis_tac [R_MODEL_SYSTEM_ORTHOJOIN_J_UNION, M_IN_Ps_W] >>
          gs[] >> ‘M A ⊆ j (M A ∪ M B)’ suffices_by metis_tac[SUBSET_DEF] >>
          irule SUBSET_TRANS >> qexists_tac ‘M A ∪ M B’ >> strip_tac
          >- simp[SUBSET_UNION]
          >- (irule lemma6_3_1 >> rw[]
              >- metis_tac[to_CS_IS_COVER, R_MODEL_SYSTEM_R_COVER_SYSTEM]
              >- (irule Upset_UNION >> metis_tac[R_MODEL_SYSTEM_PS_UPSET, M_IN_Ps_W])
             )
         )
     )
  >- (drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_or >> 
      rw[IMP_def, SUBSET_DEF] 
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename[‘(RCS.E ⬝ x) ∈ Orthojoin (M A) (M B)’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x, M_SUBSET_RCS_W, SUBSET_DEF] >> 
          ‘Orthojoin (M A) (M B) = j (M A ∪ M B)’ by metis_tac [R_MODEL_SYSTEM_ORTHOJOIN_J_UNION, M_IN_Ps_W] >>
          gs[] >> ‘M B ⊆ j (M A ∪ M B)’ suffices_by metis_tac[SUBSET_DEF] >>
          irule SUBSET_TRANS >> qexists_tac ‘M A ∪ M B’ >> strip_tac
          >- simp[SUBSET_UNION]
          >- (irule lemma6_3_1 >> rw[]
              >- metis_tac[to_CS_IS_COVER, R_MODEL_SYSTEM_R_COVER_SYSTEM]
              >- (irule Upset_UNION >> metis_tac[R_MODEL_SYSTEM_PS_UPSET, M_IN_Ps_W])
             )
         )
     )
  >- (drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_and >> 
      drule_then strip_assume_tac Model_Function_or >> 
      rw[IMP_def, SUBSET_DEF] 
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename[‘(RCS.E ⬝ x) ∈ RCS.W’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >> 
          gs[])
      >- (rename[‘(RCS.E ⬝ x) ⬝ y ∈ M C’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >> 
          ‘Orthojoin (M A) (M B) = j (M A ∪ M B)’ by metis_tac [R_MODEL_SYSTEM_ORTHOJOIN_J_UNION, M_IN_Ps_W] >>
          gs[] >> qpat_x_assum ‘_ ∈ j _’ mp_tac >> rw[j_def] >>
          ‘Z ▹ y’ by gs[to_CS_def] >>
          ‘Localized (M C)’ by
            metis_tac [Is_Prop_def, corollary6_4_2, M_IN_Ps_W, M_SUBSET_RCS_W, R_MODEL_SYSTEM_PS_UPSET,
                       R_MODEL_SYSTEM_PS_ORTHOCLOSED, R_MODEL_SYSTEM_R_COVER_SYSTEM] >>
          gs[Localized_def] >> pop_assum mp_tac >> rw[SUBSET_DEF, j_def] >>
          pop_assum irule >> simp[PULL_EXISTS] >> qexists_tac ‘Z ⬝ x’ >> rw[] 
          >- (‘(Z ⬝ x) ▹ (x ⬝ y)’ suffices_by simp[to_CS_def] >>
              ‘y ∈ RCS.W’ by gs[to_CS_def] >>
              ‘(Z ⬝ x) ▹ (y ⬝ x)’ suffices_by
                metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_FUSION_COMM] >>
              irule RCS_FUSION_COVERING >> metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM]
             )
          >- (gs[op_Lift_1, SUBSET_DEF] >> rename[‘z ⬝ x ∈ M C’] >>
              first_x_assum $ qspec_then ‘z’ strip_assume_tac >> gs[] >>
              metis_tac[RCS_FUSION_COMM, M_SUBSET_RCS_W, SUBSET_DEF, R_MODEL_SYSTEM_R_COVER_SYSTEM]
             )
          >- (‘x ⬝ y ∈ RCS.W’ suffices_by simp[to_CS_def] >>
              ‘y ∈ RCS.W’ by gs[to_CS_def] >>
              metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_FUSION_CLOSURE]
             )
         )
     )
  >- (drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_and >> 
      drule_then strip_assume_tac Model_Function_or >> 
      rw[IMP_def, SUBSET_DEF] 
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename[‘RCS.E ⬝ x ∈ Orthojoin (M A ∩ M B) (M A ∩ M C)’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x, M_SUBSET_RCS_W, SUBSET_DEF] >>
          ‘Orthojoin (M B) (M C) = j (M B ∪ M C)’ by metis_tac [R_MODEL_SYSTEM_ORTHOJOIN_J_UNION, M_IN_Ps_W] >>
          ‘Orthojoin (M A ∩ M B) (M A ∩ M C) = j ((M A ∩ M B) ∪ (M A ∩ M C))’ by
            metis_tac [R_MODEL_SYSTEM_ORTHOJOIN_J_UNION, M_IN_Ps_W] >> 
          gs[] >> qpat_x_assum ‘x ∈ j (M B ∪ M C)’ mp_tac >> rw[j_def] >>
          qexists_tac ‘Z’ >>
          ‘Z ⊆ M A’ suffices_by
            metis_tac[SUBSET_DEF, UNION_OVER_INTER, SUBSET_INTER] >>
          irule SUBSET_TRANS >> qexists_tac ‘{w | x ≼ w ∧ w ∈ RCS.W}’ >> reverse $ rw[]
          >- (‘Upset (M A)’ by metis_tac[M_IN_Ps_W, R_MODEL_SYSTEM_PS_UPSET] >>
              gs[Upset_def] >> rw[SUBSET_DEF] >> last_x_assum irule >> rw[to_CS_def] >>
              metis_tac[]
             )
          >- (‘{w | x ≼ w ∧ w ∈ RCS.W} = Up (to_CS RCS) {x}’ by
                (rw[Up_def, Once EXTENSION, to_CS_def] >> metis_tac[]) >>
              gs[] >> irule (Is_Cover_System_def |> iffLR |> cj 4) >>
              metis_tac[to_CS_IS_COVER, R_MODEL_SYSTEM_R_COVER_SYSTEM, to_CS_def]
             )
         )
     )
  >- (drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_not >>
      rw[IMP_def, SUBSET_DEF] 
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename[‘RCS.E ⬝ x ∈ RCS.W’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >> 
          gs[])
      >- (rename[‘(RCS.E ⬝ x) ⬝ y ∈ Perp (M A)’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >> 
          gs[Perp_def] >> rpt strip_tac
          >- metis_tac[M_SUBSET_RCS_W, SUBSET_DEF, R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_FUSION_CLOSURE]
          >- (rename[‘(x ⬝ y) ⊥ z’] >> last_x_assum $ qspec_then ‘x ⬝ z’ strip_assume_tac >>
              ‘∀x'. x' ∈ M B ⇒ (x ⬝ z) ⊥ x'’ by metis_tac[M_SUBSET_RCS_W, SUBSET_DEF] >>
              irule RCS_CONTRAPOSITION >>
              metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, M_SUBSET_RCS_W, SUBSET_DEF]
             )
         )
     )
  >- (drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_not >>
      rw[IMP_def, SUBSET_DEF] 
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename[‘RCS.E ⬝ x ∈ M A’] >> 
          ‘(RCS.E ⬝ x) = x’ by (gs[Perp_def] >> metis_tac[E_x_is_x]) >> 
          gs[] >> ‘M A = Perp (Perp (M A))’ suffices_by metis_tac[] >>
          metis_tac[M_IN_Ps_W, R_MODEL_SYSTEM_PS_ORTHOCLOSED]
         )
     )
  >- (‘C_Holds RCS Ps M RCS.E p’ by gs[] >>
      ‘C_Holds RCS Ps M RCS.E p'’ by gs[] >>
      drule_then strip_assume_tac Model_Function_and >>
      gs[C_Holds_def]
     )
  >- (‘C_Holds RCS Ps M RCS.E p’ by gs[] >>
      ‘C_Holds RCS Ps M RCS.E (p --> p')’ by gs[] >>
      drule_then strip_assume_tac Model_Function_imp >>
      gs[C_Holds_def, IMP_def, SUBSET_DEF] >> last_x_assum irule >>
      qexists_tac ‘RCS.E’ >> simp[] >>
      metis_tac[RCS_FUSION_RIGHT_IDENTITY, R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
     )
  >- (‘C_Holds RCS Ps M RCS.E p’ by gs[] >> 
      drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_t >>
      gs[C_Holds_def, IMP_def, SUBSET_DEF] >> rw[]
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (‘Upset (M p)’ by metis_tac[M_IN_Ps_W, R_MODEL_SYSTEM_PS_UPSET] >>
          gs[Upset_def] >> last_x_assum irule >> rw[]
          >- (‘RCS.E ⬝ x' ∈ RCS.W’ suffices_by rw[to_CS_def] >>
              metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_FUSION_LEFT_IDENTITY])
          >- (qexists_tac ‘RCS.E’ >> simp[] >>
              ‘RCS.E ≼ (RCS.E ⬝ x')’ suffices_by rw[to_CS_def] >>
              ‘(RCS.E ⬝ RCS.E) ≼ (RCS.E ⬝ x')’ suffices_by
                metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_FUSION_LEFT_IDENTITY] >>
              irule RCS_FUSION_MONO_REFINEMENT >> simp[] >>
              metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_PREORDER, PreOrder, reflexive_def])
         )
     )  
  >- (‘C_Holds RCS Ps M RCS.E (τ --> p)’ by gs[] >> 
      drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_t >>
      gs[C_Holds_def, IMP_def, SUBSET_DEF] >>
      last_x_assum irule >>
      qexists_tac ‘RCS.E’ >> 
      metis_tac[RCS_FUSION_RIGHT_IDENTITY, R_MODEL_SYSTEM_R_COVER_SYSTEM,
                RCS_PREORDER, PreOrder, reflexive_def])                
QED


val _ = export_theory();
