#lang racket

(require redex/reduction-semantics)
(require rackunit)



(define-language Simple
  ;; Expressions
  (e ::=

     ;; Terminals.
     c
     p

     ;; Reference acquisition.
     (& r ω x)

     ;; Variable binding.
     (letvar x : t = e e) ;; bind x of type τ to the result of e, place at ρ

     ;; Region binding.
     (letrgn [r] e)

     ;; Structured control flow
     (if e e e))   ;; predication, "the only interesting thing"
     ;;                             -Christos Dimoulas, Ph.D.
     ;;                               5/9/2024


  ;; Constants
  (c ::= i true false ())
  (i ::= integer)

  ;; Place expressions.
  (p ::=
     x     ;; variable
     (* p)) ;; dereference
     ;; (. p i) ;; tuple indexing


  ;; Variables.
  (x ::= variable-not-otherwise-mentioned)

  ;; Region
  (ρ ::=
     r ;; concrete region
     ϱ) ;; abstract region

  ;; Concrete region variables.
  (r ::= variable-not-otherwise-mentioned)
  ;; Abstract region variables.
  (ϱ ::= variable-not-otherwise-mentioned)


  ;; Ownership qualifiers.
  (ω ::= shared unique)

  ;; Types
  (t ::=
     unit      ;; unit type
     int       ;; integer type
     bool      ;; boolean type
     (& ρ ω t)) ;; reference type

     ;; α              ;; type variable
     ;; ((t ...) -> t) ;; function type



  #:binding-forms
  (letvar x : t = e e #:refers-to x)
  (letrgn [r] e #:refers-to r))


(default-language Simple)

;; Extended language for the typechecker.
(define-extended-language Simple+Γ Simple
  ;; Combined environment.
  (Γ  ::= (Γv Γr))
  ;; Variable envirnment.
  (Γv ::= ((x : t) ...))
  ;; Region/provenance environment.
  (Γr ::= ((r ↦ loans) ...))
  ;; List of loans.
  (loans ::= {(ω p) ...})
  ;; List of places.
  (πs ::= ((p ...) ...)))


(define-judgment-form Simple+Γ
  #:mode (⊢ I I O O)
  #:contract (⊢ Γ e t Γ) ;; Take Γ and e, produce t (type of e) and new Γ

  [-------------- "unit"
   (⊢ Γ () unit Γ)]

  [-------------- "integer"
   (⊢ Γ integer int Γ)]

  [--------------- "bool true"
   (⊢ Γ true bool Γ)]

  [--------------- "bool false"
   (⊢ Γ false bool Γ)]

  [----------------------- "variable"
   (⊢ Γ x (lookup-var x Γ) Γ)]

  [ ;; TODO: the hard part :3
   ;; Γ(r) = ∅
   (side-condition (empty? (lookup-rgn r Γ)))
   ;; Γ ⊢ω p => { ℓ }
   (⊢ω Γ () ω x loans)
   ;; Γ ⊢ω p : t

   (⊢ Γ x t Γ_x)
   ------------------------------------------------ "T-Borrow"
   (⊢ Γ (& r ω x) (& r ω t) (extend-rgn r loans Γ))]

  [(⊢ (Γv Γr) e_bind t (Γv_bind Γr_bind))
   (⊢ (extend-var x t (Γv Γr_bind)) e_body t_body (Γv_body Γr_body))
   ----------------------------------------------------------------- "variable declaration"
   (⊢ (Γv Γr) (letvar x : t = e_bind e_body) t_body (Γv Γr_body))]

  [(⊢ (extend-rgn r {} Γ) e t Γ_e)
   ---------------------------------------- "region binding"
   (⊢ Γ (letrgn [r] e) t (drop-rgn r Γ_e))]


  ;; ⋓ requires that types of bound variables in the two stack
  ;; typings be equal (which potentially demands use of T-Drop when typing the branches), and unions
  ;; the loan sets for each region 𝑟 from both stack typings
  [(⊢ (Γv Γr) e_cond bool Γ_cond)
   (⊢ (Γv Γr) e_then t (Γv_then Γr_then))
   (⊢ (Γv Γr) e_else t (Γv_else Γr_else))
   ----------------------------------------------------------------- "branch"
   (⊢ (Γv Γr) (if e_cond e_then e_else) t (Γv (⋓ Γr_then Γr_else)))])



(define-judgment-form Simple+Γ
  #:mode (⊢ω I I I I O)
  #:contract (⊢ω Γ πs ω p loans)
  ;; p is ω-safe under Γ, with reborrow-exlusion list π-, and may point to any of the loas in the borrow chain { ^ω p }


  ;; Check if a place π is ω-safe by looking at each loan in every region r' in Γ and either:
  [ ;; (1) if either that loan or ω is unique, then π does not overlap with the loan
   (side-condition (∀# ω p Γr))
   -------------------------------------- "O-SafePlace-Loan-Aliasing"
   (⊢ω (Γv Γr) πs ω p {(ω p)})])

  ;; [ ;; (2) all references in Γ with region r' are in the reborrow exclusion list
  ;;  ;; TODO
  ;;  -------------------------------------- "O-SafePlace-Exclusion"
  ;;  (⊢ω (Γv Γr) πs ω p {(ω p)})]





;; BEGIN ∀#

(define-metafunction Simple+Γ
  ∀# : ω p Γr -> boolean
  ;; unique place aliases with something. womp womp.
  [(∀# unique p {(r ↦ [(ω p) (ω_rest p_rest) ...])
                 (r_rest ↦ loans_rest) ...}) #f]

  ;; shared place aliases with a unique loan. womp womp.
  [(∀# shared p {(r ↦ [(unique p) (ω_rest p_rest) ...])
                 (r_rest ↦ loans_rest) ...}) #f]

  ;; Iterate over the loan set.
  [(∀# ω p {(r ↦ [(ω_other p_other)
                  (ω_rest p_rest) ...])
            (r_rest ↦ loans_rest) ...})
   (∀# ω p {(r ↦ [(ω_rest p_rest) ...])
            (r_rest ↦ loans_rest) ...})]

  ;; End of loan set.
  [(∀# ω p {(r ↦ [])
            (r_rest ↦ loans_rest) ...})
   (∀# ω p {(r_rest ↦ loans_rest) ...})]

  ;; End of Γr
  [(∀# ω p {}) #t])


;; Tests for ∀#


(test-equal
 (term (∀# unique x {(r ↦ [(unique x)])}))
 #f)


(test-equal
 (term (∀# shared x {(r ↦ [(shared x)])}))
 #t)


(test-equal
 (term (∀# shared x {(r ↦ [(unique definitely-not-x)])}))
 #t)


(test-equal
 (term (∀# shared x {(r ↦ [(unique x)])}))
 #f)


;; END ∀#




(define-metafunction Simple+Γ
  [(same? t_1 t_1) #t]
  [(same? t_1 t_2) #f])


(define-metafunction Simple+Γ
  extend-var : x t Γ -> Γ
  [(extend-var x t (((x_Γ : t_Γ) ...) Γr))
   (((x : t) (x_Γ : t_Γ) ...) Γr)])


(define-metafunction Simple+Γ
  lookup-var : x Γ -> t
  [(lookup-var x
               (((x : t) (x_2 : t_2) ...) Γr))
   t]
  [(lookup-var x
               (((x_1 : t_1) (x_2 : t_2) ...)
                Γr))
   (lookup-var x
               (((x_2 : t_2) ...)
                Γr))])


(define-metafunction Simple+Γ
  insert-rgn : r loans Γr -> Γr
  [(insert-rgn r loans ((r_first ↦ loans_first) ... (r ↦ loans_other) (r_rest ↦ loans_rest) ...))
   ((r_first ↦ loans_first) ... (r ↦ loans) (r_rest ↦ loans_rest) ...)]
  [(insert-rgn r loans ((r_rest ↦ loans_rest) ...))
   ((r ↦ loans) (r_rest ↦ loans_rest) ...)])


(define-metafunction Simple+Γ
  extend-rgn : r loans Γ -> Γ
  [(extend-rgn r loans (Γv Γr))
   (Γv (insert-rgn r loans Γr))])


(define-metafunction Simple+Γ
  lookup-rgn : r Γ -> loans
  [(lookup-rgn r
               (Γv
                ((r ↦ loans) (r_2 ↦ loans_2) ...)))
   loans]
  [(lookup-rgn r (Γv ((r_1 ↦ loans_1) (r_2 ↦ loans_2) ...)))
   (lookup-rgn r (Γv ((r_2 ↦ loans_2) ...)))])


(define-metafunction Simple+Γ
  drop-rgn : r Γ -> Γ
  [(drop-rgn r (Γv ((r ↦ loans) (r_Γ ↦ loans_Γ) ...)))
   (Γv ((r_Γ ↦ loans_Γ) ...))]
  [(drop-rgn r (Γv ((r_other ↦ loans_other) (r_Γ ↦ loans_Γ) ...)))
   (drop-rgn r (Γv ((r_Γ ↦ loans_Γ) ...)))])



(define-metafunction Simple+Γ
  ⋃ : loans loans -> loans ;; \union : set union of two loan sets.
  [(⋃ loans ()) loans]
  [(⋃ ((ω_1 p_1) ...) ((ω p) (ω_rest p_rest) ...))
   (⋃ ((ω_1 p_1) ... (ω p)) ((ω_rest p_rest) ...))
   (side-condition (not (member (term (ω p)) (term ((ω_1 p_1) ...)))))]
  [(⋃ loans ((ω p) (ω_rest p_rest) ...))
   (⋃ loans ((ω_rest p_rest) ...))])


;; Test for ⋃
(test-equal
 (term (⋃ ((unique x)) ((unique x))))
 (term ((unique x))))

(test-equal
 (term (⋃ ((unique x)) ((unique x) (shared y))))
 (term ((unique x) (shared y))))




;; BEGIN ⋓

(define-metafunction Simple+Γ
  ⋓ : Γr Γr -> Γr ;; \Cup : union the loan sets of then and else.
  [(⋓ Γr_1 ()) Γr_1]
  [(⋓ () Γr_2) Γr_2]
  [(⋓ ((r ↦ loans_1)
       (r_rest1 ↦ loans_rest1) ...) ;; we will iterate over the first environment.
      ((r_before2 ↦ loans_before2)
       ...
       (r ↦ loans_2)
       (r_rest2 ↦ loans_rest2) ...))
   (insert-rgn r (⋃ loans_1 loans_2)
               (⋓ ((r_rest1 ↦ loans_rest1) ...)
                  ((r_before2 ↦ loans_before2) ... (r_rest2 ↦ loans_rest2) ...)))])


;; Tests for ⋓
(test-equal
 (term (⋓ [(r1 ↦ {(unique x)})] [(r1 ↦ {(unique y)})]))
 (term [(r1 ↦ {(unique x) (unique y)})]))


;; END ⋓



;; Tests for ⊢.
(define-term Γ_empty (() ()))
(test-judgment-holds (⊢ Γ_empty 1 int any))
(test-judgment-holds (⊢ Γ_empty true bool any))
(test-judgment-holds (⊢ Γ_empty false bool any))
(test-judgment-holds (⊢ Γ_empty (letvar x : int = 1 x) int any))
(test-judgment-holds (⊢ Γ_empty (letvar x : bool = false x) bool any))
(test-judgment-holds (⊢ Γ_empty
                        (letvar x : bool = false (letvar y : bool = true x))
                        bool
                        any))
(test-judgment-holds (⊢ Γ_empty
                        (letvar x : bool = true (if x 100 200))
                        int
                        any))

;; #;(test-judgment-holds (⊢ Γ_empty
;;                         (letrgn [rz]
;;                                 (letvar x : bool = true
;;                                         (letvar y : bool = false
;;                                                 (letvar z : (& rz unique bool) = (if x (& rz unique x) (& rz unique y))
;;                                                         z))))
;;                         (& r unique bool)
;;                         any))

(test-equal
 (judgment-holds (⊢ Γ_empty (letvar x : int = false x) bool any))
 #false)

;; References
(test-judgment-holds (⊢ Γ_empty
                        (letvar x : int = 0
                                (letrgn [r1] (& r1 unique x)))
                        (& r unique int)
                        any))

;; First, we need to make this test fail by seeing that r1 and r2 alias.
;; Then, we need to make this test pass by seeing that r1 is dropped once r2 borrows x.
;; (test-judgment-holds
;;  (⊢ Γ_empty
;;     (letvar x : int = 0
;;             (letrgn
;;              [r1]
;;              (letrgn
;;               [r2]
;;               (letvar
;;                y : (& r1 unique int) = (& r1 unique x)
;;                (letvar z : (& r2 unique int) = (& r2 unique x) z)))))
;;     (& r unique int)
;;     any))

;; This test should fail, because we are borrowing from x in r1 and r2.
(test-equal
 (judgment-holds
  (⊢ Γ_empty
     (letvar x : int = 0
             (letrgn
              [r1]
              (letrgn
               [r2]
               (letvar
                y : (& r1 unique int) = (& r1 unique x)
                (letvar z : (& r2 unique int) = (& r2 unique x) y)))))
     (& r unique int)
     any))
 #false)

(test-judgment-holds
 (⊢ ({(x : int)} {(r ↦ ())})
    (& r unique x)
    (& r unique int)
    ({(x : int)} {(r ↦ ((unique x)))})))

(test-judgment-holds
 (⊢ Γ_empty
    (letvar x : int = 0
            (letrgn [r1]
                    (letrgn [r2]
                            (if x
                                (letvar y : (& r1 unique int) = (& r1 unique x) 100)
                                200
                                ;; (letvar z : (& r2 unique int) = (& r2 unique x) 200)
                                ))))
    int
    any))


(test-results)
