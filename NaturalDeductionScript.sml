open HolKernel Parse boolLib bossLib stringTheory;

open GoldblattRLTheory;

val _ = new_theory "NaturalDeduction";

val _ = set_fixity "-->" (Infixr 490);
val _ = overload_on ("-->", “g_IMP”);

val _ = set_fixity "&" (Infixr 490); 
val _ = overload_on ("&", “g_AND”);

val _ = overload_on ("~", “g_NOT”);
    
val _ = overload_on ("τ", “g_tt”);

val _ = set_fixity "V" (Infixr 490);
val _ = overload_on ("V", “g_OR”);
    
val _ = set_fixity "<->" (Infixr 490);
val _ = overload_on ("<->", “g_DIMP”);
 
val _ = set_fixity "∘ᵣ" (Infixr 490);
val _ = overload_on ("∘ᵣ", “g_ICONJ”);

Datatype: Bunch = PROP g_prop
          | COMMA Bunch Bunch
          | SEMICOLON Bunch Bunch
End

val _ = overload_on ("p:", “PROP”); 
        
val _ = set_fixity "," (Infixr 460);
val _ = overload_on (",", “COMMA”); 

val _ = set_fixity ";" (Infixr 460);
val _ = overload_on (";", “SEMICOLON”); 

Datatype: B_Context = HOLE
          | LCOMMA B_Context Bunch
          | RCOMMA Bunch B_Context
          | LSEMI B_Context Bunch
          | RSEMI Bunch B_Context
End

Definition REPLACE_def:
  (REPLACE HOLE X = X) ∧
  (REPLACE (LCOMMA Γ b) X = COMMA (REPLACE Γ X) b) ∧ 
  (REPLACE (RCOMMA b Γ) X = COMMA b (REPLACE Γ X)) ∧
  (REPLACE (LSEMI Γ b) X  = SEMICOLON (REPLACE Γ X) b) ∧ 
  (REPLACE (RSEMI b Γ) X  = SEMICOLON b (REPLACE Γ X)) 
End
     
Inductive R_sequent:
(* Classical Rules *)
[Assumption:] (∀A. R_sequent (p:A) A) ∧
[AND_Elimination_l:] (∀A B. R_sequent (p:(A & B)) A) ∧
[AND_Elimination_r:] (∀A B. R_sequent (p:(A & B)) B) ∧
[OR_Introduction_l:] (∀A B. R_sequent (p:A) (A V B)) ∧
[OR_Introduction_r:] (∀A B.R_sequent (p:B ) (A V B)) ∧
[NOT_NOT_Introduction:] (∀A. R_sequent (p:A) (~(~A))) ∧ 
[NOT_NOT_Elimination:] (∀A. R_sequent (p:(~(~A))) A) ∧
(* Non-Classical Rule *)
[AND_Introduction:] (∀X Y A B. (R_sequent X A ∧ R_sequent Y B ⇒ R_sequent (X, Y) (A & B))) ∧
[IMP_Introduction:] (∀X A B. R_sequent (X; (p:A)) B ⇒ R_sequent X (A --> B)) ∧
[IMP_Elimination:] (∀X Y A B. R_sequent X (A --> B) ∧ R_sequent Y A ⇒ R_sequent (X; Y) B) ∧
[RAA:] (∀X Y A B. R_sequent (X; (p:A)) B ∧ R_sequent Y (~B) ⇒ R_sequent (X; Y) (~A)) ∧
[OR_Elimination:] (∀Γ X A B C. R_sequent(REPLACE Γ (p: A)) C ∧ R_sequent (REPLACE Γ (p: B)) C ∧ R_sequent X (A V B)
                               ⇒ R_sequent (REPLACE Γ X) C) ∧
(* Structual Rules *)
[COMMA_commutative:] (∀Γ X Y A. R_sequent (REPLACE Γ (X,Y)) A ⇒ R_sequent (REPLACE Γ (Y,X)) A) ∧
[COMMA_associative_lr:] (∀Γ X Y Z A. R_sequent (REPLACE Γ ((X, Y), Z)) A ⇒ R_sequent (REPLACE Γ (X, (Y, Z))) A) ∧
[COMMA_associative_rl:] (∀Γ X Y Z A. R_sequent (REPLACE Γ (X, (Y, Z))) A ⇒ R_sequent (REPLACE Γ ((X, Y), Z)) A) ∧
[COMMA_idempotent_lr:] (∀Γ X A. R_sequent (REPLACE Γ (X,X)) A ⇒ R_sequent (REPLACE Γ X) A) ∧
[COMMA_idempotent_rl:] (∀Γ X A. R_sequent (REPLACE Γ X) A ⇒ R_sequent (REPLACE Γ (X,X)) A) ∧
[weakening:] (∀Γ X Y A. R_sequent (REPLACE Γ X) A ⇒ R_sequent (REPLACE Γ (X,Y)) A) ∧
[identity_lr:] (∀Γ X A. R_sequent (REPLACE Γ ((p:τ) ;X) ) A ⇒ R_sequent (REPLACE Γ X) A) ∧
[identity_rl:] (∀Γ X A. R_sequent (REPLACE Γ X) A ⇒ R_sequent (REPLACE Γ ((p:τ) ;X) ) A) ∧
(* system R *)
[SEMICOLON_commuative:]  (∀Γ X Y A. R_sequent (REPLACE Γ (X;Y)) A ⇒ R_sequent (REPLACE Γ (Y;X)) A) ∧
[SEMICOLON_associative_lr:] (∀Γ X Y Z A. R_sequent (REPLACE Γ ((X; Y); Z)) A ⇒ R_sequent (REPLACE Γ (X; (Y; Z))) A) ∧
[SEMICOLON_idempotent:] (∀Γ X A. R_sequent (REPLACE Γ (X;X)) A ⇒ R_sequent (REPLACE Γ X) A)
End



val _ = overload_on ("|-", “goldblatt_provable”);

val _ = set_fixity "||-" (Infixr 490);
val _ = overload_on ("||-", “R_sequent”);

Theorem SEMICOLON_associative_rl:
  ∀Γ X Y Z A. R_sequent (REPLACE Γ (X; (Y; Z))) A ⇒ R_sequent (REPLACE Γ ((X; Y); Z)) A
Proof
  metis_tac [SEMICOLON_associative_lr, SEMICOLON_commuative]
QED

Theorem NOT_NOT_replacement:
  ∀X A. (X ||- A) ⇔ (X ||- ~~A)
Proof
  rpt strip_tac >> EQ_TAC
  >- (‘(p:τ) ||- A --> ~~A’ by metis_tac[NOT_NOT_Introduction, identity_rl, IMP_Introduction, REPLACE_def] >> 
      metis_tac[IMP_Elimination, identity_lr, REPLACE_def])
  >- (‘(p:τ) ||- ~~A --> A’ by metis_tac[NOT_NOT_Elimination, identity_rl, IMP_Introduction, REPLACE_def] >> 
      metis_tac[IMP_Elimination, identity_lr, REPLACE_def])
QED

Theorem R_Contrapositive:
  ∀ A B. (p:(A-->B) ; p:~B) ||- ~A
Proof
  metis_tac[RAA, IMP_Elimination, Assumption]
QED

Theorem OR_Introduction_gen:
  ∀X A B. (X ||- A ⇒ X ||- (A V B)) ∧
          (X ||- A ⇒ X ||- (B V A))
Proof
  rw[] 
  >- (‘p:τ ||- A --> (A V B)’ by
        metis_tac [OR_Introduction_l, Assumption, IMP_Introduction, identity_rl, REPLACE_def] >> 
      metis_tac [IMP_Elimination, REPLACE_def, identity_lr, SEMICOLON_commuative])
  >- (‘p:τ ||- A --> (B V A)’ by
        metis_tac [OR_Introduction_r, Assumption, IMP_Introduction, identity_rl, REPLACE_def] >> 
      metis_tac [IMP_Elimination, REPLACE_def, identity_lr, SEMICOLON_commuative])
QED
     
Theorem R_sequent_completeness:
  ∀A. goldblatt_provable A ⇒ R_sequent (p: τ) A
Proof
  Induct_on ‘goldblatt_provable’ >> rpt strip_tac
  >- metis_tac [Assumption, identity_rl, IMP_Introduction, REPLACE_def]
  >- (‘(((p:(A --> B)) ; (p:(B --> C))) ; p:A) ||- C’ suffices_by 
        metis_tac [identity_rl, IMP_Introduction, REPLACE_def] >>
      assume_tac Assumption >>
      last_assum $ qspec_then ‘A --> B’ strip_assume_tac >>
      last_assum $ qspec_then ‘B --> C’ strip_assume_tac >>       
      last_x_assum $ qspec_then ‘A’ strip_assume_tac >> 
      ‘(p:(A-->B) ; p:A) ||- B’ by metis_tac[IMP_Elimination] >>       
      ‘(p:(B --> C) ; p:(A-->B) ; p:A) ||- C’ by metis_tac[IMP_Elimination] >>       
      assume_tac SEMICOLON_associative_rl >> 
      last_x_assum $ qspecl_then [‘HOLE’,‘p: (B --> C)’, ‘p: (A --> B)’, ‘p:A’, ‘C’] strip_assume_tac >> 
      gs[REPLACE_def] >> 
      assume_tac SEMICOLON_commuative >>
      last_x_assum $ qspecl_then [‘LSEMI HOLE (p:A)’,‘p: (B --> C)’, ‘p: (A --> B)’, ‘C’] strip_assume_tac >> 
      gs[REPLACE_def]
     )
  >- (‘((p: A) ; (p:(A-->B))) ||- B’ suffices_by
        metis_tac [Assumption, identity_rl, IMP_Introduction, REPLACE_def] >>
      assume_tac Assumption >>
      last_assum $ qspec_then ‘A --> B’ strip_assume_tac >>
      last_x_assum $ qspec_then ‘A’ strip_assume_tac >>
      assume_tac SEMICOLON_commuative >>
      last_x_assum $ qspecl_then [‘HOLE’,‘p: (A --> B)’, ‘p:A’, ‘B’] strip_assume_tac >>
      metis_tac [REPLACE_def, IMP_Elimination]
     )
  >- (‘(p:(A-->A-->B) ; p:A) ||- B ’ suffices_by
        metis_tac [Assumption, identity_rl, IMP_Introduction, REPLACE_def] >> 
      ‘((p:(A-->A-->B) ; p:A) ; p:A)  ||- B ’ by
        metis_tac [Assumption, IMP_Elimination] >>
      metis_tac [REPLACE_def, SEMICOLON_associative_lr, SEMICOLON_idempotent]
     )
  >- metis_tac[AND_Elimination_l, Assumption, IMP_Introduction, identity_rl, REPLACE_def]
  >- metis_tac[AND_Elimination_r, Assumption, IMP_Introduction, identity_rl, REPLACE_def]
  >- (‘(p: ((A --> B) & (A --> C)) ; p:A) ||- (B & C)’ suffices_by
        metis_tac [Assumption, identity_rl, IMP_Introduction, REPLACE_def] >>
      ‘(p: ((A --> B) & (A --> C)) ; p:A) ||- B’ by
        metis_tac[IMP_Elimination, Assumption, AND_Elimination_l] >> 
      ‘(p: ((A --> B) & (A --> C)) ; p:A) ||- C’ by
        metis_tac[IMP_Elimination, Assumption, AND_Elimination_r] >>
      metis_tac[AND_Introduction, COMMA_idempotent_lr, REPLACE_def]
     )
  >- metis_tac[OR_Introduction_l, Assumption, IMP_Introduction, identity_rl, REPLACE_def]
  >- metis_tac[OR_Introduction_r, Assumption, IMP_Introduction, identity_rl, REPLACE_def]
  >- (‘(p: ((A --> C) & (B --> C)) ; p:(A V B)) ||- C’ suffices_by
        metis_tac [Assumption, identity_rl, IMP_Introduction, REPLACE_def] >> 
      ‘(p: ((A --> C) & (B --> C)) ; p:A) ||- C’ by 
        metis_tac[IMP_Elimination, Assumption, AND_Elimination_l] >> 
      ‘(p: ((A --> C) & (B --> C)) ; p:B) ||- C’ by 
        metis_tac[IMP_Elimination, Assumption, AND_Elimination_r] >>
      assume_tac OR_Elimination >>
      last_x_assum $ qspecl_then [‘RSEMI (p: ((A --> C) & (B --> C))) HOLE’, 
                                  ‘p: (A V B)’, ‘A’, ‘B’, ‘C’] strip_assume_tac >>
      metis_tac [Assumption, REPLACE_def]
     )
  >- (‘(p: (A & B V C)) ||- ((A & B) V A & C)’ suffices_by
        metis_tac [Assumption, identity_rl, IMP_Introduction, REPLACE_def] >>
      ‘(p: (A & B V C)) ||- A’ by metis_tac[Assumption, AND_Elimination_l] >>
      ‘(p: (A & B V C)) ||- (B V C)’ by metis_tac[Assumption, AND_Elimination_r] >>
      ‘(p: (A & B V C) , p:B ) ||- ((A & B) V (A & C))’ by 
        metis_tac [Assumption, AND_Introduction, OR_Introduction_gen] >>
      ‘(p: (A & B V C) , p:C ) ||- ((A & B) V (A & C))’ by 
        metis_tac [Assumption, AND_Introduction, OR_Introduction_gen] >>
      assume_tac OR_Elimination >>
      last_x_assum $ qspecl_then [‘RCOMMA (p:(A & B V C)) HOLE’,
                                  ‘p:(A & B V C)’, ‘B’, ‘C’,
                                  ‘((A & B) V A & C)’] strip_assume_tac >>      
      metis_tac [COMMA_idempotent_lr, REPLACE_def]
     )
  >- (‘((p:(A --> ~B)) ; p:(B)) ||- (~A)’ suffices_by 
        metis_tac [identity_rl, IMP_Introduction, REPLACE_def] >> 
      irule RAA >> metis_tac [NOT_NOT_Introduction, Assumption, IMP_Elimination]
     )
  >- metis_tac [identity_rl, IMP_Introduction, REPLACE_def, NOT_NOT_Elimination]
  >- metis_tac[AND_Introduction, REPLACE_def, COMMA_idempotent_lr]
  >- metis_tac[IMP_Elimination, identity_lr, REPLACE_def]
  >- metis_tac[IMP_Introduction, identity_rl, REPLACE_def]
  >- metis_tac[Assumption, IMP_Elimination, identity_lr, REPLACE_def] 
QED




Val _ = export_theory();
