
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

val _ = export_theory();
