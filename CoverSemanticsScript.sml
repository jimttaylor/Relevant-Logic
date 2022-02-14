
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

Theorem Lemma6_3_1:
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

Definition Is_Relevant_Cover_System_def:
  Is_Relevant_Cover_System RCS ⇔
    RCS.E ∈ RCS.W ∧ 
    (∀x y. RCS.REF x y ⇒ x ∈ RCS.W ∧ y ∈ RCS.W) ∧
    (∀x Z. RCS.COVER Z x ⇒ x ∈ RCS.W ∧ Z ⊆ RCS.W) ∧
    (∀x y. x ∈ RCS.W ∧ y ∈ RCS.W ⇒ RCS.FUSE x y ∈ RCS.W) ∧
    (∀x y. RCS.ORTH x y ⇒ x ∈ RCS.W ∧ y ∈ RCS.W) ∧
    Is_Cover_System <| W := RCS.W; REF := RCS.REF; COVER := RCS.COVER |> ∧

    (* SQUARE-DECREASING COMMUNITIVE ORDERED MONOID *)
    (∀x. x ∈ RCS.W ⇒ RCS.FUSE x RCS.E = x) ∧
    (∀x. x ∈ RCS.W ⇒ RCS.FUSE RCS.E x = x) ∧
    (∀x y. x ∈ RCS.W ∧ y ∈ RCS.W ⇒ RCS.FUSE x y = RCS.FUSE y x) ∧
    (∀x y z. x ∈ RCS.W ∧ y ∈ RCS.W ∧ z ∈ RCS.W ⇒ RCS.FUSE x (RCS.FUSE y z) = RCS.FUSE (RCS.FUSE x y) z) ∧
    (∀ x x' y y'. RCS.REF x x' ∧ RCS.REF y y' ⇒ RCS.REF (RCS.FUSE x y) (RCS.FUSE x' y')) ∧
    (∀ x. x ∈ RCS.W ⇒ RCS.REF (RCS.FUSE x x) x) ∧
    
    (* OTHER *)
    (∀ x y Z. RCS.COVER Z x ⇒ RCS.COVER {RCS.FUSE z y | z ∈ Z} (RCS.FUSE x y)) ∧
    (∀ x x' y y'. RCS.REF x x' ∧ RCS.REF y y' ∧ RCS.ORTH x y ⇒ RCS.ORTH x' y') ∧
    (∀ x Z. RCS.COVER {z | z ∈ Z ∧ RCS.ORTH z RCS.E} x ⇒ RCS.ORTH x RCS.E) ∧
    (∀x y z. x ∈ RCS.W ∧ y ∈ RCS.W ∧ z ∈ RCS.W ∧ RCS.ORTH (RCS.FUSE x y) z ⇒ RCS.ORTH (RCS.FUSE x z) y)
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


Definition to_CS_def[simp]:
  (to_CS: α R_COVER_SYSTEM -> α COVER_SYSTEM) RCS = <|W := RCS.W; REF := RCS.REF; COVER := RCS.COVER |>
End

Theorem RCS_PREORDER:
  Is_Relevant_Cover_System RCS ⇒
  PreOrder RCS.REF
Proof
  rw[] >> ‘Is_Cover_System (to_CS RCS)’ by simp[RCS_COVER_SYSTEM] >>
  gs[Is_Cover_System_def]
QED
        
Definition Orthocompliment_def:
  Orthocompliment RCS X = {y | y ∈ RCS.W ∧ ∀x. x ∈ X ⇒ RCS.ORTH y x}
End


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
        
Theorem lemma6_4_1_1:
  ∀RCS x y. Is_Relevant_Cover_System RCS ∧ x ∈ RCS.W ∧ y ∈ RCS.W ⇒
            (RCS.ORTH x y ⇔ RCS.ORTH (RCS.FUSE x y) RCS.E)
Proof
  rw[EQ_IMP_THM]
  >- (irule RCS_CONTRAPOSITION >> simp[RCS_IDENTITY] >>
      ‘RCS.FUSE x RCS.E = x’ by metis_tac[RCS_FUSION_RIGHT_IDENTITY] >> gs[]
     )
  >- (drule_then strip_assume_tac RCS_CONTRAPOSITION >>
      pop_assum $ qspecl_then [‘x’, ‘y’, ‘RCS.E’]  strip_assume_tac >>
      ‘RCS.FUSE x RCS.E = x’ by metis_tac[RCS_FUSION_RIGHT_IDENTITY] >> 
      gs[RCS_IDENTITY]
     )
QED
        
Theorem lemma6_4_1_2:
  ∀RCS X. Is_Relevant_Cover_System RCS ∧ X ⊆ RCS.W ⇒
          Is_Prop RCS (Orthocompliment RCS X)
Proof
  reverse $ rw[Is_Prop_def, Localized_def, Orthocompliment_def] 
  >- (rw[Upset_def, SUBSET_DEF] >> irule RCS_REFINEMENT_ORTHOGONAL >>
      simp[] >> qexistsl_tac [‘d’, ‘x’] >> simp[] >>
      metis_tac[PreOrder, RCS_PREORDER, reflexive_def])
  >- (rw[j_def, Once SUBSET_DEF] >> rename[‘RCS.ORTH x y’] >>
      irule (iffRL lemma6_4_1_1) >> rw[]
      >- gs[SUBSET_DEF] >>
      ‘∀z. z ∈ Z ⇒ RCS.ORTH z y’ by
        (rw[] >> gs[SUBSET_DEF]) >> 
      ‘∀z. z ∈ Z ⇒ RCS.ORTH (RCS.FUSE z y) RCS.E’ by
        (rw[] >> irule (iffLR lemma6_4_1_1) >>
         gs[SUBSET_DEF]) >>
      drule_then strip_assume_tac RCS_FUSION_COVERING >> 
      pop_assum $ qspecl_then [‘x’, ‘y’, ‘Z’] strip_assume_tac >>
      gs[] >> irule RCS_IDENTITY_ORTH_IS_LOCAL >> simp[] >> 
      qexists_tac ‘{RCS.FUSE z y | z ∈ Z}’ >>
      ‘{z | z ∈ {RCS.FUSE z y | z ∈ Z} ∧ RCS.ORTH z RCS.E} =
       {RCS.FUSE z y | z ∈ Z}’ suffices_by simp[] >> 
      rw[EXTENSION, EQ_IMP_THM] >> metis_tac[])
QED

Theorem lemma6_4_1_3:
  ∀RCS X Y. Is_Relevant_Cover_System RCS ∧ X ⊆ RCS.W ∧
            Y ⊆ RCS.W ∧ Upset (to_CS RCS) Y ⇒
            Upset (to_CS RCS) (IMP RCS X Y)
Proof
  rw[Upset_def]
  >- simp[IMP_def, Once SUBSET_DEF]
  >- (rw[IMP_def, SUBSET_DEF] >> rename [‘x ∈ X’, ‘d ∈ IMP RCS X Y’] >>
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
            Y ⊆ RCS.W ∧ Localized (to_CS RCS) Y ⇒
            Localized (to_CS RCS) (IMP RCS X Y)
Proof
  rw[SUBSET_DEF, Localized_def, IMP_def, j_def] >>
  rename[‘RCS.FUSE x y ∈ Y’] >> first_x_assum irule >>
  simp[RCS_FUSION_CLOSURE] >> qexists_tac ‘{RCS.FUSE z y | z ∈ Z}’ >> rw[]
  >- simp[RCS_FUSION_COVERING]
  >- (first_x_assum $ qspec_then ‘z’ strip_assume_tac >> gs[] >>
      last_x_assum irule >> metis_tac[]
     )
QED

Theorem lemma6_4_1_5:
  ∀RCS x X. Is_Relevant_Cover_System RCS ∧ x ∈ RCS.W ∧ X ⊆ RCS.W ∧
            (∀y. y ∈ X ⇒ RCS.ORTH x y) ⇒
            (∀y. y ∈ j (to_CS RCS) X ⇒ RCS.ORTH x y)
Proof
  rw[j_def] >> irule (iffRL lemma6_4_1_1) >> simp[] >>
  irule RCS_IDENTITY_ORTH_IS_LOCAL >> simp[] >>
  qexists_tac ‘{RCS.FUSE z x | z ∈ Z}’ >>
  ‘{z | z ∈ {RCS.FUSE z x | z ∈ Z} ∧ RCS.ORTH z RCS.E}
   = {RCS.FUSE z x | z ∈ Z}’ by 
    (rw[EXTENSION, EQ_IMP_THM] >> metis_tac[RCS_FUSION_COMM, lemma6_4_1_1, SUBSET_DEF]) >>
  gs[] >>
  ‘RCS.COVER {RCS.FUSE z x | z ∈ Z} (RCS.FUSE y x)’ suffices_by
    metis_tac[RCS_FUSION_COMM] >>
  irule RCS_FUSION_COVERING >> simp[]
QED



val _ = export_theory();
