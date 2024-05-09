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
     (letvar x : t = e) ;; bind x of type τ to the result of e, place at ρ
     (x : t = e)

     ;; Region binding.
     (letrgn [r] e)
     
     ;; Structured control flow
     {e e ...} ;; sequencing, racket doesnt like ;
     ;; (if e e e)   ;; predication
     ;; (while e e)  ;; recursion
     )

  ;; Constants
  (c ::= i true false ())
  (i ::= integer)
  
  ;; Place expressions.
  (p ::=
     x     ;; variable
     ;; (* p) ;; dereference
     ;; (. p i) ;; tuple indexing
     )

  ;; Variables.
  (x ::= variable-not-otherwise-mentioned)

  ;; Provenance
  (ρ ::=
     r ;; concrete provenance
     ϱ ;; abstract provenance
     )
  ;; Concrete provenance variables.
  (r ::= variable-not-otherwise-mentioned)
  ;; Abstract provenance variables.
  (ϱ ::= variable-not-otherwise-mentioned)


  ;; Ownership qualifiers.
  (ω ::= shared unique)

  ;; References.

  ;; Types
  (t ::=
     unit      ;; unit type
     int       ;; integer type
     bool      ;; boolean type
     (& ρ ω t) ;; reference type

     ;; α              ;; type variable
     ;; ((t ...) -> t) ;; function type
     )


  #:binding-forms
  (letvar x : t = e) #:exports x
  (letrgn [r] e #:refers-to r)
  )

(default-language Simple)

;; Extended language for the typechecker.
(define-extended-language Simple+Γ Simple
  (Γ ::= ((x t) ...))
  )

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
   (⊢ Γ x (lookup x Γ) Γ)]

  [ ;; TODO: the hard part :3
   ;; Γ(r) = ∅
   ;; Γ ⊢ω p => { ℓ }
   ;; Γ ⊢ω p : t
   (⊢ Γ x t Γ_x)
   ----------------- "borrow"
   (⊢ Γ (& r ω x) (& r ω t) Γ)]

  [(⊢ Γ e t Γ_e)
   --------------------------------------------- "variable declaration"
   (⊢ Γ (letvar x : t = e) unit (extend x t Γ))]

  [(⊢ Γ e t Γ_e)
   ---------------------- "variable definition"
   (⊢ Γ (x : t = e) unit Γ)]
  
  [(⊢ Γ e t Γ_e)
   ------------------------- "region binding"
   (⊢ Γ (letrgn [p] e) t Γ)]

  [(⊢ Γ e t Γ_e)
   -------------- "sequencing end"
   (⊢ Γ {e} t Γ)]
  
  [(⊢ Γ e_1 t_1 Γ_1)
   (⊢ Γ_1 {e_2 e_rest ...} t_rest Γ_rest)
   -------------------------------------- "sequencing"
   (⊢ Γ {e_1 e_2 e_rest ...} t_rest Γ)  ]
  
  )

(define-metafunction Simple+Γ
  [(same? t_1 t_1) #t]
  [(same? t_1 t_2) #f]
  )

(define-metafunction Simple+Γ
  extend : x t Γ -> Γ
  [(extend x t ((x_Γ t_Γ) ...)) ((x t) (x_Γ t_Γ) ...)]
  )

(define-metafunction Simple+Γ
  lookup : x Γ -> t
  [(lookup x ((x t)     (x_2 t_2) ...)) t]
  [(lookup x ((x_1 t_1) (x_2 t_2) ...)) (lookup x ((x_2 t_2) ...))]
  )

;; Tests for the typechecker.
(test-judgment-holds (⊢ () 1 int any))
(test-judgment-holds (⊢ () true bool any))
(test-judgment-holds (⊢ () false bool any))
(test-judgment-holds (⊢ () (letvar x : int = 1) unit any))
(test-judgment-holds (⊢ () (letvar x : bool = false) unit any))
(test-judgment-holds (⊢ ()
                        {(letvar x : bool = false)
                         (letvar y : bool = true)
                         x}
                        bool
                        any))
(test-judgment-holds (⊢ ()
                        {(letvar x : int = 0)
                         (x : int = 1)
                         x}
                        int any))

(test-equal
 (judgment-holds (⊢ () (letvar x : int = false) int any))
 #false)

(test-equal
 (judgment-holds (⊢ () (letvar x : int = false) bool any))
 #false)

(test-equal
 (judgment-holds (⊢ () {(letvar x : int = false) x} int any))
 #false)

(test-results)
