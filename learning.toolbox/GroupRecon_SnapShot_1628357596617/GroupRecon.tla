------------------------------- MODULE GroupRecon -------------------------------

EXTENDS Integers

VARIABLE withdrawId, withdrawStream, clientAPIDatabase, groupReconConsumer, groupReconPayouts

Init == withdrawId = 0
     /\ withdrawStream = {}
     /\ clientAPIDatabase = {}
     /\ groupReconConsumer = {}
     /\ groupReconPayouts = {}
     
TypeOK == withdrawStream \subseteq Nat
       /\ clientAPIDatabase \subseteq withdrawStream
       /\ groupReconConsumer \subseteq withdrawStream
       /\ groupReconPayouts \subseteq groupReconConsumer
       
PayoutIsAvailableInClientAPI == groupReconPayouts \subseteq clientAPIDatabase

ProduceWithdraw == withdrawId' = withdrawId + 1
                /\ withdrawStream' = withdrawStream \union { withdrawId' }
                /\ UNCHANGED <<clientAPIDatabase, groupReconConsumer, groupReconPayouts>>
                
ClientAPIConsume == clientAPIDatabase' = clientAPIDatabase \union withdrawStream
                 /\ UNCHANGED <<withdrawId, withdrawStream, groupReconConsumer, groupReconPayouts>>
                 
GroupReconWithdrawConsume == groupReconConsumer' = groupReconConsumer \union clientAPIDatabase
                          /\ UNCHANGED <<withdrawId, withdrawStream, clientAPIDatabase, groupReconPayouts>>
                          
GeneratePayouts == groupReconPayouts' = groupReconPayouts \union groupReconConsumer
                /\ UNCHANGED <<withdrawId, withdrawStream, groupReconConsumer, clientAPIDatabase>>

Done == 3 \in groupReconPayouts

Next == ProduceWithdraw
     \/ ClientAPIConsume
     \/ GroupReconWithdrawConsume
     \/ GeneratePayouts

=============================================================================
\* Modification History
\* Last modified Sat Aug 07 19:33:09 CEST 2021 by rchaves
\* Created Sat Aug 07 18:53:17 CEST 2021 by rchaves
