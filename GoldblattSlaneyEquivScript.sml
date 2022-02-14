




open HolKernel Parse boolLib bossLib stringTheory;

open SlaneyRLTheory GoldblattRLTheory;
     
val _ = new_theory "GoldblattSlaneyEquiv";

Definition sg_translation_def:
  (sg_translation (s_VAR A) = g_VAR A) ∧
  (sg_translation (A -->ₛ B) = sg_translation A -->ₐ sg_translation B) ∧
  (sg_translation (A &ₛ B) = sg_translation A &ₐ sg_translation B) ∧
  (sg_translation (A Vₛ B) = sg_translation A Vₐ sg_translation B) ∧
  (sg_translation (A ioₛ B) = sg_translation A ioₐ sg_translation B) ∧
  (sg_translation (~ₛ A) = ~ₐ (sg_translation A)) ∧
  (sg_translation τₛ = τₐ)
End

Definition gs_translation_def:
  (gs_translation (g_VAR A) = s_VAR A) ∧
  (gs_translation (A -->ₐ B) = gs_translation A -->ₛ gs_translation B) ∧
  (gs_translation (A &ₐ B) = gs_translation A &ₛ gs_translation B) ∧
  (gs_translation (~ₐ A) = ~ₛ (gs_translation A)) ∧
  (gs_translation τₐ = τₛ)
End

val _ = overload_on ("sg", “sg_translation”);
val _ = overload_on ("gs", “gs_translation”);


Theorem gs_EQ_VAR:
  ∀A B. gs A = s_VAR B ⇔ A = g_VAR B
Proof
  rpt strip_tac >> EQ_TAC
  >- (Cases_on ‘A’ >> simp[gs_translation_def])
  >- simp [gs_translation_def]
QED

Theorem gs_EQ_IMP: 
  ∀A B C. gs A = B -->ₛ C
          ⇔ ∃ B0 C0. A = B0 -->ₐ C0 ∧ B = gs B0 ∧ C = gs C0
Proof
  Cases_on ‘A’ >> simp[gs_translation_def]
  >> metis_tac[]
QED
        
Theorem gs_EQ_AND:
  ∀A B C. gs A = B &ₛ C
          ⇔ ∃ B0 C0. A = B0 &ₐ C0 ∧ B = gs B0 ∧ C = gs C0 
Proof
  Cases_on ‘A’ >> simp[gs_translation_def] >> 
  metis_tac []
QED

Theorem gs_EQ_NOT:
∀A B. gs A = ~ₛ B ⇔ ∃ B0. A = ~ₐ B0 ∧ B = gs B0
Proof
  Cases_on ‘A’ >> simp[gs_translation_def] >>
  metis_tac []                    
QED

Theorem gs_EQ_TRUE:
  ∀A. gs A = τₛ ⇔ A = τₐ
Proof
  rpt strip_tac >> EQ_TAC
  >- (Cases_on ‘A’ >> simp[gs_translation_def])
  >- simp[gs_translation_def] 
QED

        

Theorem sg_EQ_VAR:
  sg A = g_VAR B ⇔ A = s_VAR B
Proof
  Cases_on ‘A’ >> simp[sg_translation_def, g_OR_def, g_ICONJ_def]
QED

Theorem sg_EQ_IMP:
  ∀A B C. sg A = B -->ₐ C
           ⇔ ∃ B0 C0. B = sg B0 ∧ C = sg C0 ∧ A = B0 -->ₛ C0
Proof
   Cases_on ‘A’ >> simp[sg_translation_def, g_OR_def, g_ICONJ_def]
   >> metis_tac[]
QED

                
Theorem sg_EQ_AND:
  ∀A B C. sg A = B &ₐ C
          ⇔ ∃ B0 C0. A = B0 &ₛ C0 ∧ B = sg B0 ∧ C = sg C0
Proof
   Cases_on ‘A’ >> simp[sg_translation_def, g_OR_def, g_ICONJ_def]
   >> metis_tac[]
QED

Theorem sg_EQ_NOT:
  ∀A B. sg A = ~ₐ B
        ⇔ ∃ B0 C0. (A = ~ₛ B0 ∧ B = sg B0) ∨
                   (A = B0 Vₛ C0 ∧ B = sg (~ₛ B0 &ₛ ~ₛ C0)) ∨
                   (A = B0 ioₛ C0 ∧ B = sg ( B0 -->ₛ ~ₛ C0))
Proof
  Cases_on ‘A’ >> simp[sg_translation_def, g_OR_def, g_ICONJ_def]
   >> metis_tac[]
QED

Theorem sg_EQ_TRUE:
  ∀A. sg A = τₐ ⇔ A = τₛ
Proof
  Cases_on ‘A’ >> simp[sg_translation_def, g_OR_def, g_ICONJ_def]
QED


Theorem sg_trans_equiv:
  ∀A B. sg A = sg B ⇒ slaney_provable(A <->ₛ B)
Proof
  Induct_on ‘B’ >> rpt strip_tac >> gs[sg_translation_def]
  >- metis_tac[s_equiv_identity, sg_EQ_VAR]
  >- ( assume_tac sg_EQ_IMP >> last_x_assum $ qspecl_then [‘A’, ‘sg B’, ‘sg B'’] strip_assume_tac >> 
       gs[] >> last_x_assum $ qspec_then ‘B0’ strip_assume_tac >> 
       last_x_assum $ qspec_then ‘C0’ strip_assume_tac >> gs[s_double_dimp_equiv]
     ) 
  >- ( assume_tac sg_EQ_AND >> last_x_assum $ qspecl_then [‘A’, ‘sg B’, ‘sg B'’] strip_assume_tac >> 
       gs[] >>  last_x_assum $ qspec_then ‘B0’ strip_assume_tac >>
       last_x_assum $ qspec_then ‘C0’ strip_assume_tac >> gs[s_double_dimp_equiv]
      )
  >- ( gs[g_OR_def] >> assume_tac sg_EQ_NOT >>
       last_x_assum $ qspecl_then [‘A’, ‘sg (~ₛ B &ₛ ~ₛ B')’] strip_assume_tac
       >> gs[sg_translation_def]
       >- ( assume_tac sg_EQ_AND >> last_x_assum $ qspecl_then [‘B0’, ‘sg (~ₛ B)’, ‘sg (~ₛ B')’] strip_assume_tac >>
            gs[sg_translation_def] >> 
            assume_tac sg_EQ_NOT >>
            last_assum $ qspecl_then [‘B0'’, ‘sg B’] strip_assume_tac >> 
            last_x_assum $ qspecl_then [‘C0’, ‘sg B'’] strip_assume_tac >>
            gs[] >>
            metis_tac[s_double_dimp_equiv, s_equiv_transitivity, s_equiv_symmetry, s_OR_definable, s_equiv_stronger_replacement, s_IO_definable]
          )          
       >- metis_tac[s_double_dimp_equiv]
     )
  >- (gs[g_ICONJ_def] >> assume_tac sg_EQ_NOT >>
       last_x_assum $ qspecl_then [‘A’, ‘sg (B -->ₛ ~ₛ B')’] strip_assume_tac
      >> gs[sg_translation_def]
      >- ( assume_tac sg_EQ_IMP >> last_x_assum $ qspecl_then [‘B0’, ‘sg B’, ‘sg (~ₛ B')’] strip_assume_tac >> 
           gs[sg_translation_def] >>
           assume_tac sg_EQ_NOT >> last_x_assum $ qspecl_then [‘C0’, ‘sg B'’] strip_assume_tac >>
           gs[] >>
           metis_tac[s_double_dimp_equiv, s_equiv_transitivity, s_equiv_symmetry, s_OR_definable, s_equiv_stronger_replacement, s_IO_definable]
         )
      >- metis_tac[s_double_dimp_equiv]
     )
  >-(assume_tac sg_EQ_NOT >> last_x_assum $ qspecl_then [‘A’, ‘sg B’] strip_assume_tac
     >> gs[]
     >> metis_tac[s_double_dimp_equiv, s_equiv_transitivity, s_equiv_symmetry, s_OR_definable, s_equiv_stronger_replacement, s_IO_definable]
    )
  >- metis_tac[s_equiv_identity, sg_EQ_TRUE]
QED

Theorem gs_trans_injective:
∀ A B. gs A = gs B ⇒ A = B
Proof
  Induct_on ‘A’
  >- metis_tac [gs_EQ_VAR]
  >- metis_tac [gs_EQ_IMP]
  >- metis_tac [gs_EQ_AND]
  >- metis_tac [gs_EQ_NOT]
  >- metis_tac [gs_EQ_TRUE]
QED
        
Theorem gs_sg_equiv:
  ∀A B. gs $ sg A = gs $ sg B ⇒ slaney_provable(A <->ₛ B)
Proof
  metis_tac[gs_trans_injective, sg_trans_equiv] 
QED

Theorem gs_sg_equiv_1:
  ∀A. ∃B. slaney_provable (A <->ₛ (gs $ sg B))
Proof
  Induct_on ‘A’ >> rpt strip_tac >> gs[]
  >- (qexists_tac ‘s_VAR s’ >> gs[gs_translation_def, sg_translation_def, s_equiv_identity])
  >- (qexists_tac ‘B -->ₛ B'’ >> gs[gs_translation_def, sg_translation_def, s_double_dimp_equiv])
  >- (qexists_tac ‘B &ₛ B'’ >> gs[gs_translation_def, sg_translation_def, s_double_dimp_equiv])
  >- (qexists_tac ‘B Vₛ B'’ >> gs[gs_translation_def, sg_translation_def, g_OR_def] >> 
      assume_tac s_OR_definable >>
      last_x_assum $ qspecl_then [‘gs $ sg B’, ‘gs $ sg B'’] strip_assume_tac >> 
      ‘slaney_provable ((A Vₛ A') <->ₛ (gs $ sg B) Vₛ (gs $ sg B'))’ suffices_by metis_tac[s_equiv_symmetry, s_equiv_transitivity]
      >> simp[s_DIMP_def] >> irule s_adjunction_rule >> strip_tac >> 
      metis_tac [s_equiv_replacement, s_equiv_stronger_replacement, s_double_dimp_equiv, slaney_provable_rules]
     )
  >- (qexists_tac ‘B ioₛ B'’ >> gs[gs_translation_def, sg_translation_def, g_ICONJ_def] >> 
      assume_tac s_IO_definable >>
      last_x_assum $ qspecl_then [‘gs $ sg B’, ‘gs $ sg B'’] strip_assume_tac >> 
      ‘slaney_provable ((A ioₛ A') <->ₛ (gs $ sg B) ioₛ (gs $ sg B'))’ suffices_by metis_tac[s_equiv_symmetry, s_equiv_transitivity]
      >> simp[s_DIMP_def] >> irule s_adjunction_rule >> strip_tac >> 
      metis_tac [s_equiv_replacement, s_equiv_stronger_replacement, s_double_dimp_equiv, slaney_provable_rules]
     )
  >- (qexists_tac ‘~ₛ B’ >> gs[gs_translation_def, sg_translation_def] >> metis_tac[s_equiv_replacement, s_DIMP_def, slaney_provable_rules])
  >- (qexists_tac ‘τₛ’ >> simp[s_equiv_identity, gs_translation_def, sg_translation_def])
QED
        


Theorem sg_gs_EQ:
  ∀A. sg $ gs A = A  
Proof
  Induct_on ‘A’ >> simp[gs_translation_def, sg_translation_def]
QED


Theorem g_trans_invarient:
  ∀A. goldblatt_provable $ sg $ gs A ⇔ goldblatt_provable A
Proof
  simp[sg_gs_EQ]
QED

Theorem gs_OR_not_in_range:
  ∀A B. ¬ ∃ C. gs C = A Vₛ B
Proof
  rpt strip_tac >> Cases_on ‘C’ >> gs[gs_translation_def]
QED

Theorem gs_IO_not_in_range:
  ∀A B. ¬ ∃ C. gs C = A ioₛ B
Proof
  rpt strip_tac >> Cases_on ‘C’ >> gs[gs_translation_def]
QED


Theorem s_trans_invarient:
  ∀A. slaney_provable $ gs $ sg A ⇔ slaney_provable A
Proof
  strip_tac >> EQ_TAC >> Induct_on ‘slaney_provable’ >> rpt strip_tac >> 
  gs[gs_translation_def, sg_translation_def, g_OR_def, g_ICONJ_def]
  >- (gvs[gs_EQ_IMP, sg_EQ_IMP] >> metis_tac[gs_sg_equiv, s_conjunction_r, s_conjunction_l, s_DIMP_def, s_modus_ponens])
  >- (gvs[gs_EQ_IMP, sg_EQ_IMP] >> rename [‘(A -->ₛ B -->ₛ C) -->ₛ B' -->ₛ A' -->ₛ C'’] >>
      ‘slaney_provable ((A -->ₛ B -->ₛ C) <->ₛ (A' -->ₛ B' -->ₛ C'))’ by
        metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement] >> 
      metis_tac [s_equiv_replacement, s_permutation]
      )
  >- (gvs[gs_EQ_IMP, sg_EQ_IMP] >> rename [‘(A -->ₛ B) -->ₛ (B' -->ₛ C) -->ₛ (A' -->ₛ C')’] >> 
      ‘slaney_provable (((B' -->ₛ C) -->ₛ A' -->ₛ C') <->ₛ (B' -->ₛ C') -->ₛ A' -->ₛ C')’ by
        metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement] 
      >> metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_transitivity]
     )
  >- (gvs[gs_EQ_IMP, sg_EQ_IMP] >> rename [‘(A -->ₛ A' -->ₛ B) -->ₛ A'' -->ₛ B'’] >> 
      ‘slaney_provable ((A -->ₛ A' -->ₛ B) <->ₛ  (A -->ₛ A -->ₛ B))’ by
        metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement] >>
      metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_contraction]
     )
  >- (gvs[gs_EQ_IMP, sg_EQ_IMP, gs_EQ_AND, sg_EQ_AND] >> 
       metis_tac[gs_sg_equiv, s_equiv_replacement, s_conjunction_l]
     )
  >- (gvs[gs_EQ_IMP, sg_EQ_IMP, gs_EQ_AND, sg_EQ_AND] >> 
       metis_tac[gs_sg_equiv, s_equiv_replacement, s_conjunction_r]
     )  
  >- (gvs[gs_EQ_IMP, sg_EQ_IMP, gs_EQ_AND, sg_EQ_AND] >> rename [‘((A -->ₛ B) &ₛ A' -->ₛ C) -->ₛ (A'' -->ₛ B' &ₛ C')’] >> 
      ‘slaney_provable (((A -->ₛ B) &ₛ A' -->ₛ C) <->ₛ ((A'' -->ₛ B) &ₛ A'' -->ₛ C))’ by
        metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement] >> 
      metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_conj_introduction] 
     )
  >- metis_tac[gs_EQ_IMP, sg_EQ_IMP, gs_OR_not_in_range]
  >- metis_tac[gs_EQ_IMP, sg_EQ_IMP, gs_OR_not_in_range]
  >- metis_tac[gs_EQ_IMP, sg_EQ_IMP, gs_EQ_AND, sg_EQ_AND, gs_OR_not_in_range]
  >- metis_tac[gs_EQ_IMP, sg_EQ_IMP, gs_EQ_AND, sg_EQ_AND, gs_OR_not_in_range]
  >- (gvs[gs_EQ_IMP, sg_EQ_IMP, gs_EQ_NOT, sg_EQ_NOT] 
      >- metis_tac[gs_sg_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_contrapositive]
      >- (rename [‘(A -->ₛ ~ₛ B) -->ₛ B' -->ₛ C Vₛ D’] >> 
         assume_tac s_OR_definable >> last_x_assum $ qspecl_then [‘C’, ‘D’] strip_assume_tac >> 
          ‘slaney_provable ((B' -->ₛ C Vₛ D) <->ₛ  B' -->ₛ ~ₛ (~ₛ C &ₛ ~ₛ D))’ by
            metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement] >>
          metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_contrapositive] 
         )
      >- (rename [‘(A -->ₛ ~ₛ B) -->ₛ B' -->ₛ C ioₛ D’] >> 
         assume_tac s_IO_definable >> last_x_assum $ qspecl_then [‘C’, ‘D’] strip_assume_tac >> 
          ‘slaney_provable ((B' -->ₛ C ioₛ D) <->ₛ  B' -->ₛ ~ₛ (C -->ₛ ~ₛ D))’ by
            metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement] >>
          metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_contrapositive] 
         )             
      >-(rename [‘(A -->ₛ C Vₛ D) -->ₛ B -->ₛ ~ₛ A'’] >>
         assume_tac s_OR_definable >> last_x_assum $ qspecl_then [‘C’, ‘D’] strip_assume_tac >>
         ‘slaney_provable ((A -->ₛ C Vₛ D) <->ₛ  A -->ₛ ~ₛ (~ₛ C &ₛ ~ₛ D))’ by
           metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement] >>
         metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_contrapositive]
        )
      >- (rename [‘(A -->ₛ C Vₛ D) -->ₛ B -->ₛ C' Vₛ D'’] >> 
          ‘slaney_provable ((A -->ₛ C Vₛ D) <->ₛ  A -->ₛ ~ₛ B)’ by
            metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_equiv_transitivity, s_OR_definable] >>
          ‘slaney_provable ((B -->ₛ C' Vₛ D') <->ₛ  B -->ₛ ~ₛ A)’ by
            metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_equiv_transitivity, s_OR_definable] >>
          metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_contrapositive]
         )
      >- (rename [‘(A -->ₛ C Vₛ D) -->ₛ B -->ₛ C' ioₛ D'’] >> 
          ‘slaney_provable ((A -->ₛ C Vₛ D) <->ₛ  A -->ₛ ~ₛ B)’ by
            metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_equiv_transitivity, s_OR_definable] >>
          ‘slaney_provable ((B -->ₛ C' ioₛ D') <->ₛ  B -->ₛ ~ₛ A)’ by
            metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_equiv_transitivity, s_IO_definable] >>
          metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_contrapositive]
         )
      >-(rename [‘(A -->ₛ C ioₛ D) -->ₛ B -->ₛ ~ₛ A'’] >>
         assume_tac s_IO_definable >> last_x_assum $ qspecl_then [‘C’, ‘D’] strip_assume_tac >>
         ‘slaney_provable ((A -->ₛ C ioₛ D) <->ₛ  A -->ₛ ~ₛ ( C -->ₛ ~ₛ D))’ by
           metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement] >>
         metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_contrapositive]
        )
      >- (rename [‘(A -->ₛ C ioₛ D) -->ₛ B -->ₛ C' Vₛ D'’] >> 
          ‘slaney_provable ((A -->ₛ C ioₛ D) <->ₛ  A -->ₛ ~ₛ B)’ by
            metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_equiv_transitivity, s_IO_definable] >>
          ‘slaney_provable ((B -->ₛ C' Vₛ D') <->ₛ  B -->ₛ ~ₛ A)’ by
            metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_equiv_transitivity, s_OR_definable] >>
          metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_contrapositive]
         )
      >- (rename [‘(A -->ₛ C ioₛ D) -->ₛ B -->ₛ C' ioₛ D'’] >> 
          ‘slaney_provable ((A -->ₛ C ioₛ D) <->ₛ  A -->ₛ ~ₛ B)’ by
            metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_equiv_transitivity, s_IO_definable] >>
          ‘slaney_provable ((B -->ₛ C' ioₛ D') <->ₛ  B -->ₛ ~ₛ A)’ by
            metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_equiv_transitivity, s_IO_definable] >>
          metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_contrapositive]
         )  
     )
  >- (gvs[gs_EQ_IMP, sg_EQ_IMP, gs_EQ_NOT, sg_EQ_NOT] >>
      metis_tac[gs_sg_equiv, s_double_dimp_equiv, s_equiv_stronger_replacement, s_equiv_replacement, s_double_negation, s_OR_definable, s_IO_definable]
     )  
 >- (‘slaney_provable (A' &ₛ A'')’ by metis_tac[slaney_provable_rules] >> 
      ‘gs $ sg A = gs $ sg (A' &ₛ A'')’ by
        ( ‘gs $ sg $ gs $ sg A = gs $ sg (A' &ₛ A'')’ by metis_tac [] >> 
          metis_tac [sg_gs_EQ]) >> 
        metis_tac [gs_sg_equiv, s_equiv_replacement]
     )   
  >- (‘slaney_provable A''’ by metis_tac[slaney_provable_rules] >> 
      ‘gs $ sg A = gs $ sg A''’ by
        ( ‘gs $ sg $ gs $ sg A = gs $ sg A''’ by metis_tac [] >> 
          metis_tac [sg_gs_EQ]) >> 
        metis_tac [gs_sg_equiv, s_equiv_replacement]
     )
  >- (‘slaney_provable (A' -->ₛ B -->ₛ C)’ by metis_tac[slaney_provable_rules] >> 
      ‘gs $ sg A = gs $ sg (A' -->ₛ B -->ₛ C)’ by
        (‘gs $ sg $ gs $ sg A = gs $ sg (A' -->ₛ B -->ₛ C)’ by metis_tac [] >> 
          metis_tac [sg_gs_EQ]) >> 
        metis_tac [gs_sg_equiv, s_equiv_replacement]
     )
  >- metis_tac[gs_EQ_IMP, gs_IO_not_in_range]
  >- (‘slaney_provable (τₛ -->ₛ A')’ by metis_tac[slaney_provable_rules] >> 
      ‘gs $ sg A = gs $ sg (τₛ -->ₛ A')’ by
        (‘gs $ sg $ gs $ sg A = gs $ sg (τₛ -->ₛ A')’ by metis_tac [] >> 
         metis_tac [sg_gs_EQ]) >>
        metis_tac [gs_sg_equiv, s_equiv_replacement]
     )
  >- (‘slaney_provable (A')’ by metis_tac[slaney_provable_rules] >> 
      ‘gs $ sg A = gs $ sg (A')’ by
        (‘gs $ sg $ gs $ sg A = gs $ sg (A')’ by metis_tac [] >> 
         metis_tac [sg_gs_EQ]) >>
        metis_tac [gs_sg_equiv, s_equiv_replacement]
     )
  >- metis_tac[slaney_provable_rules]
  >- metis_tac[slaney_provable_rules]
  >- metis_tac[slaney_provable_rules]
  >- metis_tac[slaney_provable_rules]
  >- metis_tac[slaney_provable_rules]
  >- metis_tac[slaney_provable_rules]
  >- metis_tac[slaney_provable_rules]
  >- metis_tac[slaney_provable_rules]
  >- metis_tac[slaney_provable_rules]
  >- metis_tac[slaney_provable_rules, s_OR_definable, s_equiv_replacement, s_double_dimp_equiv]
  >- (assume_tac s_OR_definable >>
      last_assum $ qspecl_then [‘(gs $ sg A) &ₛ (gs $ sg B)’,
                                ‘(gs $ sg A) &ₛ (gs $ sg C)’] strip_assume_tac >>
      last_x_assum $ qspecl_then [‘gs $ sg B’, ‘gs $ sg C’] strip_assume_tac >>
      rename[‘(A &ₛ B) Vₛ (A &ₛ C)’] >>
      metis_tac[s_double_dimp_equiv, s_equiv_replacement, s_equiv_stronger_replacement, s_distribution]
     )
  >- metis_tac[slaney_provable_rules]
  >- metis_tac[slaney_provable_rules]
  >- metis_tac[slaney_provable_rules]
  >- metis_tac[slaney_provable_rules]
  >- metis_tac[slaney_provable_rules, s_IO_definable, s_equiv_replacement]
  >- metis_tac[slaney_provable_rules, s_IO_definable, s_equiv_replacement]
  >- metis_tac[slaney_provable_rules]
  >- metis_tac[slaney_provable_rules]
QED
        

        
Theorem goldblatt_implies_slaney:
  ∀A. goldblatt_provable A ⇒ slaney_provable $ gs A
Proof
  Induct_on ‘goldblatt_provable’ >> rpt strip_tac >> gs[gs_translation_def, g_OR_def] >>
  metis_tac[slaney_provable_rules, s_assertion, s_OR_definable, s_equiv_replacement, s_disjunction_OR_def]
QED
        
Theorem slaney_implies_goldblatt:
  ∀A. slaney_provable A ⇒ goldblatt_provable $ sg A
Proof
  Induct_on ‘slaney_provable ’ >> rpt strip_tac >> gs [sg_translation_def] >>
  metis_tac[goldblatt_provable_rules, g_permutation, g_io_rule]
QED
                
val _ = export_theory();
