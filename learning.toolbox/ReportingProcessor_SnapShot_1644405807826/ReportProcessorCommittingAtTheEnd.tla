-------------------------- MODULE ReportProcessorCommittingAtTheEnd --------------------------

EXTENDS Integers, Sequences, TLC, Helpers

VARIABLE payReportQueue, processed, memoryDb, retryQueue, action

PayReportItems == <<1, 2, 3, 4>>

TypeOK == 
  action \in {"consuming_pay_report", "processing_successfull", "put_in_memory_db", "put_in_retry_queue"}

Init == payReportQueue = PayReportItems
     /\ processed = <<>>
     /\ memoryDb = <<>>
     /\ retryQueue = <<>>
     /\ action = "consuming_pay_report"
  
(* Function to add the item to the processed list, unless it's already there, simulating idempotency *)
ProcessItem(item) == IF item \notin SeqToSet(processed)
                     THEN Append(processed, item)
                     ELSE processed

(* When a kafka message is processed successfully, we mark it as successfull, unless there is already *)
(* a previous message in memory db, in this case we never process it, it will go to memory db as well *)
(* directly *)
ConsumePayReportSucc == payReportQueue /= <<>>
                     /\ memoryDb = <<>>
                     /\ action = "consuming_pay_report"
                     /\ action' = "processing_successfull"
                     /\ processed' = ProcessItem(Head(payReportQueue))
                     /\ UNCHANGED <<payReportQueue, memoryDb, retryQueue>>

(* When a kafka message is processed with error, we put the message in retry queue *)
ConsumePayReportError == payReportQueue /= <<>>
                      /\ Head(payReportQueue) \notin SeqToSet(memoryDb)
                      /\ action = "consuming_pay_report"
                      /\ action' = "put_in_memory_db"
                      /\ memoryDb' = Append(memoryDb, Head(payReportQueue))
                      /\ UNCHANGED <<processed, payReportQueue, retryQueue>>
                                        
                      
(* After putting the message in memory db, we put it in retry queue *)
PutInRetryQueue == action = "put_in_memory_db"
                /\ action' = "put_in_retry_queue"
                /\ retryQueue' = Append(retryQueue, Head(payReportQueue))
                /\ UNCHANGED <<processed, memoryDb, payReportQueue>>

(* We commit to kafka either after message is processed successfully OR after is had been put on the retry queue *)
CommitToPayReport == (action = "processing_successfull" \/ action = "put_in_retry_queue")
                  /\ action' = "consuming_pay_report"
                  /\ payReportQueue' = Tail(payReportQueue)
                  /\ UNCHANGED <<processed, memoryDb, retryQueue>>
                  
(* We consume messaged from retry queue in parallel, it is only processed if sucessfully if the current item in the queue *)
(* is the same as the Head of memory db, if so, the item is taken out of the retry queue and memory db, and added to processed *)
(* list, if not, ConsumeRetryQueueError will be triggered and the item will end up in the end of the queue again *)
ConsumeRetryQueueSucc == retryQueue /= <<>>
                      /\ Head(retryQueue) = Head(memoryDb)
                      /\ processed' = ProcessItem(Head(retryQueue))
                      /\ memoryDb' = Tail(memoryDb)
                      /\ retryQueue' = Tail(retryQueue)
                      /\ UNCHANGED <<action, payReportQueue>>
                      
(* We consume messaged from retry queue in parallel, if there is an error, the message goes back to the end of the retry queue *)
ConsumeRetryQueueError == retryQueue /= <<>>
                       /\ retryQueue' = Append(Tail(retryQueue), Head(retryQueue))
                       /\ UNCHANGED <<processed, action, memoryDb, payReportQueue>>
                  
(* At any time, the consumer may panic in the middle and restart the process from the beginning *)     
PanicConsumer == action' = "consuming_pay_report"
              /\ UNCHANGED <<processed, payReportQueue, memoryDb, retryQueue>>                   

Next == ConsumePayReportSucc
     \/ ConsumePayReportError
     \/ PutInRetryQueue
     \/ ConsumeRetryQueueSucc
     \/ ConsumeRetryQueueError
     \/ CommitToPayReport
     \/ PanicConsumer

ProcessedCompleteAndInOrderInvariant ==
    IF Len(processed) > 0 THEN
        \* sequences are 1-indexed
        LET F[i \in 1..(Len(processed) + 1)] ==
            IF i > 1 /\ ~F[i-1] THEN FALSE
                                ELSE processed[i] = PayReportItems[i]
        IN F[Len(processed)]
    ELSE TRUE

=============================================================================
\* Modification History
\* Last modified Wed Feb 09 12:23:17 CET 2022 by rchavesferna
\* Created Thu Feb 03 19:11:04 CET 2022 by rchavesferna
