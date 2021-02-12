; db.lsp
;==============================================================
;       By: Jesse Wyatt
; Due Date: 04.10.03
;
;==============================================================

(load 'unify)

(setq db '(  (T (dog fido))
	     (T (brown fido))
             (T (small fido))
             (T (dog lassie))
             (T (family fido felix pavlov))
             (T (family lassie socrates leo))
             (T (gang fido felix leo lassie))
             ((dog x1) (mammal x1))
             ((mammal x2) (wb x2))
             ((cat x3) (feline x3))
             (T (cat felix))
	     (T (brown felix))
             (T (small felix))
             ((man x4) (mortal x4))
             (T (man Socrates))
             (T (man Plato))
             ((dog x5) (likes Pavlov x5))
             ((dog x6) (mortal x6))
             ((man x7) (mammal x7))
             ((feline x8) (mammal x8))
             ((lion x9) (feline x9))
             (T (lion leo))
             (T (brown leo))
             ((feline x10) (mortal x10))
             (T (likes Socrates Plato))
             ((likes Pavlov x11) (hates x11 x12))
             ((student x13) (hates x13 homework))
             (T (student John))
             (T (student Mary))
             ((and (mammal x14) (dog x14)) (hates John x14))
             ((and (brown x15) (small x15)) (likes Socrates x15))
))

;==============================================================
; PRIMARY FUNCTION CALL
;==============================================================
; Function: ?
;
; A Simple Deductive Database.
; 
; Answers queries about a database loaded into the global
; variable db. The database should be initialized as given by
; the following example: 
;
; (setq db '(
;     (T (color blue))             ; fact: blue is a color
;     (T (color red))              ; fact: red is a color
;     ((color x1) (crayon x1))     ; rule: crayons are colors
;     ((crayon x2) (holds box x2)) ; rule: a box holds crayons
;     ((crayon x3) (draw x3 x4))   ; rule: crayons draw on
;                                          anything
;     (T (broken blue))            ; fact: blue is a broken crayon
; ))
;
; The program can follow a chain of logic back as many links
; as it needs to satisfy a query. Queries are given as follows:
;
; (? '(color x))        => (BLUE RED)
; (? '(x blue))         => (COLOR)
; (? '(draw blue y))    => YES
; (? '(holds x blue))   => (BOX)
; (? '(color monkey))   => NO
; (? '(x y))            => ((COLOR . BLUE) (COLOR . RED))
; (? '(and (color x)
;          (broken x))) => (BLUE) *
;
; * AND'S do not work for multiple variables.
;
; Variables may be set below:

(setq unify-vars '(U   V   W   X   Y   Z
                   X1  X2  X3  X4  X5  X6  X7  X8  X9  X10
                   X11 X12 X13 X14 X15 X16 X17 X18 X19 X20))

;==============================================================
(defun ? (query)
   (?-format (if (and-exists query)
                 (and-cycles query T)
                 (cycle-db query db)
             )
   )
)

;==============================================================
; Function: ?-format
;
; Formats the NIL and (NIL) query answers to be more user
; friendly in the form of NO and YES, respectively.
;
;==============================================================
(defun ?-format (?-return)
   (cond (  (null ?-return)
            'NO
         )
         (  (is-null-list ?-return)
            'YES
         )
         (  T
            (*-convert ?-return unify-vars)
         )
   )
)

;==============================================================
; Function: *-convert
;
; Converts all remaining variables found in results to '*',
; which denotes "everything."
;
;==============================================================
(defun *-convert (?-return unify-vars)
   (if (null unify-vars)
       ?-return
       (apply-sub (cons (car unify-vars) '*)
                  (*-convert ?-return (cdr unify-vars))
       )
   )
)

;==============================================================
; Function: cycle-db
;
; Recursively checks each rule or fact of the database in 
; order of their input.  One full pass of the rules and facts
; (or more abstractly, predicates) is termed a "cycle" in
; this program. Returns the list produced by logically
; deducting the valid terms from each predicate (or in some
; cases, a YES or NO return).
;
;==============================================================
(defun cycle-db (pred db-tmp)
   (cond (  (null db-tmp)
            NIL
         )
         (  (atom pred)
            '(NIL)
         )
         (  T
            (list-results (test-pred (unify pred (cadar db-tmp))
                                     (caar db-tmp)
                                     (cadar db-tmp)
                          )
                          (cycle-db pred (cdr db-tmp))
            )
         )
   )
)

;==============================================================
; Function: test-pred
;
; Returns a list of results of predicate queries by calling
; calling the function test-subs if the current right-hand
; side predicate of a rule unified to produce substitutions.
; If there were no substitutions, or if the query and the 
; right-hand predicate unified without substitutions needed,
; then NIL or (NIL) are returned, respectively.
;
;==============================================================
(defun test-pred (subs rule-if rule-then)
   (cond (  (null subs)
            NIL
         )
         (  (is-null-list subs)
            '(NIL)
         )
         (  T
            (test-subs subs rule-if (apply-subs subs rule-if) rule-then)
         )
   )
)

;==============================================================
; Function: test-subs
;
; Performs new cycles on the db depending on the type of
; substitution.  Two variables, either found in the database
; will call collect-cycle, gathering all valid results. If only
; one part of the substitution is a term but a variable exists
; in it as well, then a proof-cycle is called to be sure whether
; to give an affirmitive YES / '(NIL) about the tested predicate.
; Otherwise, a proof-cycle is called, but if its true, then
; the term of the substitution is added to the results.
;
;==============================================================
(defun test-subs (subs rule-if sa-rule-if rule-then)
   (if (null subs)
       '(NIL)
       (group-results (cond (  (atom rule-if)
                               (cdar subs)
                            )
                            (  (and (is-var (caar subs))
                                    (is-var (cdar subs))
                                    (or (is-found (caar subs) rule-if)
                                        (is-found (cdar subs) rule-if)
                                    )
                               )
                               (collect-cycle sa-rule-if)
                            )
                            (  (or (is-found (caar subs) rule-if)
                                   (is-found (cdar subs) rule-if)
                               )
                               (proof-cycle sa-rule-if '(NIL))
                            )
                            (  T
                               (proof-cycle sa-rule-if (cdar subs))
                            )
                      )
                      (test-subs (cdr subs) rule-if
                                 (apply-subs subs rule-if) rule-then
                      )
       )
   )
)

;==============================================================
; Function: collect-cycle
;
; Returns the results from a tested predicate, the if-part of
; the rule from calling function test-sub.
;==============================================================
(defun collect-cycle (rule-if)
   (if  (and-exists rule-if)
        (and-cycles rule-if NIL)
        (cycle-db rule-if db)
   )
)

;==============================================================
; Function: proof-cycle
;
; Returns the result if the tested predicate, the if-part of
; the rule from calling function test-sub, returns true (either
; '(NIL) / YES or with results.
;==============================================================
(defun proof-cycle (rule-if result)
   (if (if (and-exists rule-if)
           (and-cycles rule-if NIL)
           (cycle-db rule-if db)
       )
       result
       NIL
   )
)

;==============================================================
; Function: group-results
;
; Returns the composite result of joining two results together
; to produce relationships between them. If the two results
; being joined are lists, then essentially they are
; cross-multiplied together.
;==============================================================
(defun group-results (result1 result2)
   (cond (  (or (null result1) (null result2))
            NIL
         )
         (  (atom result1)
            (group-results (list result1) result2)
         )
         (  (atom result2)
            (group-results result1 (list result2))
         )
         (  (is-null-list result1)
            result2
         )
         (  (is-null-list result2)
            result1
         )
         (  T
            (append (this-subgroup (car result1) result2)
                    (group-results (cdr result1) result2)
            )
         )
   )
)

;==============================================================
; Function: this-subgroup
;
; Returns the list of results produced when multipling a single
; "head" term with each term in the "body". Each multiplicative
; iteration is its own group.
;==============================================================
(defun this-subgroup (head body)
   (cond (  (or (null head) (null body))
            NIL
         )
         (  T
            (cons (append (list head) (car body))
                  (this-subgroup head (cdr body))
            )
         )
   )
)

;==============================================================
; Function: and-exists
;
; Returns whether or not the pred is an "and" predicate.
;==============================================================
(defun and-exists (pred)
   (if (equal 'and (car pred))
       T
       NIL
   )
)

;==============================================================
; Function: and-cycles
;
; Cycles through a list of sub-predicates determined to be from an
; "and" predicate.  And's the results together via function
; and-results.
;==============================================================
(defun and-cycles (preds is-query)
   (cond (  (null preds)
            '(NIL)
         )
         (  T
            (and-results (cycle-db (car preds) db)
                         (and-cycles (cdr preds) is-query)
                         is-query
            )
         )
   )
)

;==============================================================
; Function: and-results
;
; Performs the boolean logic of and-ing two results together,
; which means that only terms occuring in both results will
; be returned.  If is-query is true, then this function was
; called by the query, and slightly different logic should
; be used.
;==============================================================
(defun and-results (result1 result2 is-query)
   (cond (  (or (null result1) (null result2))
            NIL
         )
         (  (atom result1)
            (and-results (list result1) result2 is-query)
         )
         (  (atom result2)
            (and-results result1 (list result2) is-query)
         )
         (  (is-null-list result1)
            result2
         )
         (  (is-null-list result2)
            result1
         )
         (  T
            (append (if is-query
                        (is-found-query (car result1) result2)
                        (is-found (car result1) result2)
                    )
                    (and-results (cdr result1) result2 is-query)
            )
         )
    )
)

;==============================================================
; Function: is-found-query
;
; Determines whether the given predicate has a valid match in
; a list of predicates, results from a query. This function is
; only used when and-ing queries. If a predicate has a match,
; then the match is returned.
;==============================================================
(defun is-found-query (pred query-list)
   (cond (  (or (null pred) (null query-list))
            NIL
         )
         (  (equal pred (car query-list))
            (cons pred
                  (is-found-query pred (cdr query-list))
            )
         )
         (  (and (listp pred)
                 (is-var (cdr pred))
            )
            (is-found-query (cdr pred) query-list)
         )
         (  (and (listp (car query-list))
                 (is-var (cdar query-list))
            )
            (append (is-found-query pred (list (cdar query-list)))
                    (list (is-found-query pred (cdr query-list)))
            )
         )
         (  (is-var pred)
            (cons (car query-list)
                  (is-found-query pred (cdr query-list))
            )
         )
         (  (is-var (car query-list))
            (cons pred
                  (is-found-query pred (cdr query-list))
            )
         )
         (  T
            (is-found-query pred (cdr query-list))
         )
   )
)

;==============================================================
; Function: is-found
;
; Determines whether a term can be found in a list, and if
; so, the term is returned in a list.
;==============================================================
(defun is-found (term this-list)
   (cond (  (or (null term) (null this-list))
            NIL
         )
         (  (listp (car this-list))
            (or (is-found term (car this-list))
                (is-found term (cdr this-list))
            )
         )
         (  (equal term (car this-list))
            (list term)
         )
         (  T
            (is-found term (cdr this-list))
         )
   )
)


;==============================================================
; Function: list-results
;
; Combines two list of results into a single list.  If one of
; those results is (NIL), then it is not combined with the other
; result, which is solely returned; if both results are (NIL),
; then (NIL) is returned.
;
;==============================================================
(defun list-results (result1 result2)
   (cond (  (and (is-null-list result1)
                 (is-null-list result2)
            )
            '(NIL)
         )
         (  (and (null result1)
                 (null result2)
            )
            NIL
         )
         (  (and (not (null result1))
                 (or (is-null-list result2)
                     (null result2)
                 )
            )
            result1  
         )
         (  (and (not (null result2))
                 (or (is-null-list result1)
                     (null result1)
                 )
            )
	    result2        
         )
         (  T
            (append result1 result2)
         )
   )
)

;==============================================================
; Function: apply-subs
;
; Applies a list of substitutions to a term by cycling through
; its list of substitutions recursively and applying each, one
; at a time, to the term via a call to function apply-sub.
;
;==============================================================
(defun apply-subs (subs term)
   (if (null subs)
       term
       (apply-sub (car subs) (apply-subs (cdr subs) term))
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
;                          THE END
;==============================================================


;(trace group-results)
;(trace this-subgroup)
;(trace cycle-db)
;(trace test-subs)
;(trace and-exists)
;(trace and-cycles)
;(trace and-results)
;(trace next-cycle)
;(trace list-results)
;(trace is-found-query)
;(trace and-list)
;(trace decompose-result)
;(trace translate-results)
;(trace ?-format)
;(trace is-result)
