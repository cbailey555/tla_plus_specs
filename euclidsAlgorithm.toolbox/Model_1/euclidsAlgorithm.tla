-------------------------- MODULE euclidsAlgorithm --------------------------
EXTENDS Integers, gcd, TLC

CONSTANTS M, N
ASSUME M \in Nat \{0}
ASSUME N \in Nat \{0}


(****************************************************

--fair algorithm Euclid {
    variables x \in 1..N, y \in 1..N, x0 = x, y0 = y;
              {
                while ( x # y ) { 
                    if (x < y) { y := y - x }
                    else       { x := x - y }
                                };
                       assert (x = y) /\ (x = GCD(x0, y0))
            
             }                
              
}

*****************************************************)  

\* BEGIN TRANSLATION
VARIABLES x, y, x0, y0, pc

vars == << x, y, x0, y0, pc >>

Init == (* Global variables *)
        /\ x \in 1..N
        /\ y \in 1..N
        /\ x0 = x
        /\ y0 = y
        /\ pc = "Lbl_1"
    

         

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x # y
               THEN /\ IF x < y
                          THEN /\ y' = y - x
                               /\ x' = x
                          ELSE /\ x' = x - y
                               /\ y' = y
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert((x = y) /\ (x = GCD(x0, y0)), 
                              "Failure of assertion at line 21, column 24.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << x, y >>
         /\ UNCHANGED << x0, y0 >>


Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

PartialCorrectness == (pc = "Done") => (x = y) /\ (x = GCD(x0, y0))

(***************************************************************************
These two definitions of Lbl_1 are isomorphic to the auto-generated pluscal definition
(at least as far as TLC is concerned), and I find them much easier to read.
The mixed use of 'if then else' control flow and conjunction/disjunction is 
mad uncomfortable.
 ***************************************************************************)
(*    
IfThenElse == \/ 
                 /\ (x < y)
                 /\ (y' = y - x)
                 /\ (x' = x)
                 /\ (pc' = "Lbl_1")
              \/ 
                 /\ (y < x)
                 /\ (x' = x - y)
                 /\ (y' = y)
                 /\ (pc' = "Lbl_1")
              \/ 
                 /\ (x = y)
                 /\ (pc' = "Done")
                 /\ UNCHANGED << x, y >>
                 /\ Assert ((x = y) /\ (x = GCD(x0, y0)), "Failure of assertion at line 21, column 24.")
                 
Lbl_1 == /\ pc = "Lbl_1"
         /\ IfThenElse
         /\ UNCHANGED << x0, y0 >>
*)
    
    (*     
IfThenElse_impl == /\ (x < y) => /\ y' = y - x
                                 /\ x' = x
                                 /\ pc' = "Lbl_1"
                   /\ (x > y) => /\ x' = x - y
                                 /\ y' = y
                                 /\ pc' = "Lbl_1"
                   /\ (x = y) => /\ pc' = "Done"
                                 /\ UNCHANGED << x, y >>
                                 /\ Assert ((x = y) /\ (x = GCD(x0, y0)), "Failure of assertion at line 21, column 24.")

Lbl_1 == /\ pc = "Lbl_1"
         /\ IfThenElse_impl
         /\ UNCHANGED << x0, y0 >>
 *)


=============================================================================
\* Modification History
\* Last modified Sun Nov 11 12:23:21 CST 2018 by pnkm
\* Created Sun Nov 11 12:16:43 CST 2018 by pnkm
