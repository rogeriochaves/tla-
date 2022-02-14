---- MODULE MC ----
EXTENDS learning, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT definitions RM
const_162833167493556000 == 
{r1, r2, r3}
----

\* SYMMETRY definition
symm_162833167493557000 == 
Permutations(const_162833167493556000)
----

=============================================================================
\* Modification History
\* Created Sat Aug 07 12:21:14 CEST 2021 by rchaves
