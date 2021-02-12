; unify.lsp
;==============================================================
;       By: Jesse Wyatt
; Due Date: 04.10.03
;
;==============================================================

;==============================================================
; PRIMARY FUNCTION CALL
;==============================================================
; Function: unify
;
; An implementation of Robinson's Unification Algorithm.
;
; Returns the Most General Unifier (MGU) as a sigma value (a
; set of substitutions) that enables two terms to match
; bilaterally (that is, unify), if any substitution either way 
; is even possible. If not every substitution needed to make the
; terms unify is possible, then NIL is returned; or if the terms
; are completely equal without any substitution necessary, then
; (NIL) is returned.
;
; Examples:
;
; (unify 'A 'X)                             => ((X . A))
; (unify 'X 'A)                             => ((X . A))
; (unify 'A 'B)                             => NIL
; (unify 'X 'X)                             => (NIL)
; (unify 'A 'A)                             => (NIL)
; (unify '((F Y) W (G Z)) '(U U V))         => ((U F Y) (W F Y) (V G Z))
; (unify '(A X) '(Y (F X)))                 => NIL
; (unify '(A X (F Z)) '(Z (G (H Z)) (F A))) => ((Z . A) (X G (H A)))
;
; The variable set is defined as follows:
  (setq unify-vars '(U V W X Y Z))
; 
;==============================================================
(defun unify (term1 term2)
   (if (and (atom term1) (atom term2))
       (unify-atoms (find-sub term1 term2))
       (build-sigma term1 term2 (find-sub term1 term2))
   )
)

;==============================================================
; Function: unify-atoms
;
; This function is designed to handle the special case of
; unifying two atoms. Resolves minor formatting issues.
;
;==============================================================
(defun unify-atoms (sub)
   (if (or (null sub) (is-null-list sub))
       sub
       (list sub)
   )    
)

;==============================================================
; Function: build-sigma
;
; Recursively accumulates a set of substitutions in the form
; of (variable . value) until a passed substitution is NIL,
; at which point the function breaks recursion, and the NIL value
; returns back through the recursive calls to the point of the
; first build-sigma call (found above in match), which
; instead of the substitution set will return NIL, indicating
; that not every substitution is possible.
;
;==============================================================
(defun build-sigma (term1 term2 sub)
   (if (null sub)
       NIL
       (compose-sigma sub
                      (unify (next (apply-sub sub term1))
                             (next (apply-sub sub term2))
                      )
                      (next term1) (next term2)
       )
   )
)

;==============================================================
; Function: compose-sigma
;
; Returns the result of applying each substitution to the 
; accumulating sigma value (see build-sigma) as the substitution
; is found.
;
;==============================================================
(defun compose-sigma (sub sigma term1 term2)
   (prepend-sub (apply-sigma sigma sub)
                sigma term1 term2
   )
)

;==============================================================
; Function: prepend-sub
;
; Prepends one substitution with the next substitution found
; in the function build-sigma. If either substitution
; to be combined is NULL, then NIL is returned; if both
; substitutions are (NIL), then (NIL) is returned; if only one
; substitution is (NIL), then the other substitution is
; returned; if both are substitutions in the form of
; (variable . value), then the two substitutions are cons'ed
; together. For formating purposes, additional code is used
; to construct the proper nesting of lists.
;
;==============================================================
(defun prepend-sub (sub1 sub2 term1 term2)
   (cond (  (and (null term1) (null term2))
            (if (is-null-list sub1)
                sub1
                (list sub1)
            )
         )
         (  (or (null sub1) (null sub2))
            NIL
         )
         (  (and (is-null-list sub1) (is-null-list sub2))
            (list NIL)
         )
         (  (is-null-list sub1)
            sub2
         )
         (  (is-null-list sub2)
            (list sub1)
         )
         (  T
            (cons sub1 sub2)
         )
   ) 
)

;==============================================================
; Function: find-sub
;
; Finds the first corresponding values of the terms. To determine
; where this correspondance occurs, the cars of each term are taken
; until at least one of the terms is an atom; this corresponds
; to whatever value has been reached in the other term. Thus, 
; the parenthetical list-nesting structures of each term are 
; observed. Returns the result of testing them via the function
; test-sub.
;
;==============================================================
(defun find-sub (term1 term2)
   (cond (  (or (atom term1) (atom term2))
            (test-sub term1 term2)
         )
         (  T
            (find-sub (car term1) (car term2))
         )
   )
)

;==============================================================
; Function: test-sub
;
; Determines whether the value of the first term is equal to a
; corresponding value in the second term. If they are equal,
; then (NIL) is returned; if they are unequal and one of the
; terms is a variable, then a dotted list denoting what variable
; is replaced by what value (variable . value) is returned if
; they are unequal and neither terms are variables then NIL is
; returned. The return value serves as the substitution value
; in other functions.
;
;==============================================================
(defun test-sub (term1 term2)
   (cond (  (equal term1 term2)
	    (list NIL)
         )
         (  (is-var term1)
            (and (not-occuring term1 term2)
                 (cons term1 term2)
            )
         )
         (  (is-var term2)
            (and (not-occuring term2 term1)
                 (cons term2 term1)
            )
         )
         (  T
            NIL
         )
   )
)
;==============================================================
; Function: not-occuring
;
; Returns true if a given atomic value does not equal any atom
; in the given term; false otherwise.
;
;==============================================================
(defun not-occuring (v term)
   (if (atom term)
       (not (equal v term))
       (and (not (equal v (car term)))
            (not-occuring v (next term))
       )
   )
)

;==============================================================
; Function: apply-sigma
;
; Returns the result of applying the given sigma value to the
; given term. Each substitution in the set is individually
; applied in turn to the term via a call to function
; apply-sub.
;
;==============================================================
(defun apply-sigma (sigma term)
   (if (null sigma)
       term
       (apply-sub (car sigma) (apply-sigma (cdr sigma) term))
   )
)

;==============================================================
; Function: apply-sub
;
; Returns the result of applying the given substitution to the
; given term. Each constituent atom of the term is checked for
; equality with the variable portion (the car) of the
; substitution, and if equal, then the current atom being
; checked is replaced by the constant portion (the cdr) of the
; substitution.
;
;==============================================================
(defun apply-sub (sub term)
   (cond (  (null term)
            NIL
         )
         (  (atom term)
            (if (equal (car sub) term)
                (cdr sub)
                term
            )
         )
         (  T
            (cons (apply-sub sub (car term))
                  (apply-sub sub (cdr term))
            )
         )
   )
)

;==============================================================
; Function: is-null-list
;
; Returns true if and only if the given value is (NIL).
;
;==============================================================
(defun is-null-list (n)
   (if (and n (null (car n)))
       T
       NIL
   )
)

;==============================================================
; Function: is-var
;
; Returns true if the given symbol is a member of the legal
; variable set defined by the member function.
;
;==============================================================
(defun is-var (x) (member x unify-vars))


;==============================================================
; GENERAL UTILITY FUNCTIONS (non-specific to this program)
;==============================================================

;==============================================================
; Function: next
;
; Returns a list with its first atom removed, and the list
; retains its parenthetical nesting levels.
;
; (next '((A (B)) C)) => (((B)) C)
; (next '(A)) => NIL
; (next '(A B C)) => (B C)
;
;==============================================================
(defun next (lst)
   (cond (  (atom (shave lst))
            NIL
         )
         (  (null (cdr (shave lst)))
            NIL
         )
         (  (atom (car lst))
            (cdr lst)
         )
         (  T
            (cons-append (next (car lst)) (cdr lst))
         )
   )
)

;==============================================================
; Function: shave
;
; Returns a list or atom with all external parentheses removed.
;
; (shave '((A))) => A
;
; The outer parentheses are "shaved".
;
;==============================================================
(defun shave (lst)
   (cond (  (atom lst)
            lst
         )
         (  (null (cdr lst))
            (shave (car lst))
         )
         (  T
            lst
         )
   )
)

;==============================================================
; Function: cons-append
;
; Combines abilities of both the functions cons and append; NIL
; values at any level of list-nesting are discarded, yet other
; non-null lists are combined in a fashion that retains their
; parenthetical nesting levels.
;
; (cons-append NIL 'A) => A
; (cons-append '((NIL)) 'A) => A
; (cons-append '(A) '(B)) => '((A) B)
;
;==============================================================
(defun cons-append (lst1 lst2)
   (cond (  (and (null (shave lst1))
                 (null (shave lst2))
            )
            NIL
         )
         (  (null (shave lst1))
	    lst2
         )
         (  (null (shave lst2))
            (list lst1)
         )
         (  T
            (append (list lst1) lst2)
         )
   )
)

;==============================================================
;                          THE END
;==============================================================
