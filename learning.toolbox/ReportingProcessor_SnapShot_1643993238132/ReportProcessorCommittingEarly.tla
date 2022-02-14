------------------- MODULE ReportProcessorCommittingEarly -------------------

EXTENDS Integers, Sequences, TLC, Helpers

VARIABLE payReportQueue, currentItem, processed, memoryDb, retryQueue, action

PayReportItems == <<1, 2>>

TypeOK == 
  action \in {"consuming_pay_report", "committing", "processing_successfull", "put_in_memory_db", "put_in_retry_queue"}

Init == payReportQueue = PayReportItems
     /\ processed = <<>>
     /\ memoryDb = <<>>
     /\ retryQueue = <<>>
     /\ currentItem = 0
     /\ action = "consuming_pay_report"
  
(* Function to add the item to the processed list, unless it's already there, simulating idempotency *)
ProcessItem(item) == IF item \notin SeqToSet(processed)
                     THEN Append(processed, item)
                     ELSE processed

(* We commit to kafka immediately after taking the message out of the queue, creating a completely non-blocking queue *)
ConsumePayReport == payReportQueue /= <<>>
                 /\ action = "consuming_pay_report"
                 /\ action' = "committing"
                 /\ currentItem' = Head(payReportQueue)
                 /\ payReportQueue' = Tail(payReportQueue)
                 /\ UNCHANGED <<processed, memoryDb, retryQueue>>

(* When a kafka message is processed successfully, we mark it as successfull, unless there is already *)
(* a previous message in memory db, in this case we never process it, it will go to memory db as well *)
(* directly, then we process the next item *)
ConsumePayReportSucc == payReportQueue /= <<>>
                     /\ memoryDb = <<>>
                     /\ action = "committing"
                     /\ action' = "consuming_pay_report"
                     /\ processed' = ProcessItem(currentItem)
                     /\ UNCHANGED <<payReportQueue, currentItem, memoryDb, retryQueue>>

(* When a kafka message is processed with error, we put the message in retry queue *)
ConsumePayReportError == currentItem \notin SeqToSet(memoryDb)
                      /\ action = "committing"
                      /\ action' = "put_in_memory_db"
                      /\ memoryDb' = Append(memoryDb, currentItem)
                      /\ UNCHANGED <<currentItem, processed, payReportQueue, retryQueue>>
                                        

(* After putting the message in memory db, we put it in retry queue and process the next item *)
PutInRetryQueue == action = "put_in_memory_db"
                /\ action' = "consuming_pay_report"
                /\ retryQueue' = Append(retryQueue, currentItem)
                /\ UNCHANGED <<currentItem, processed, memoryDb, payReportQueue>>
                  
(* We consume messaged from retry queue in parallel, it is only processed if sucessfully if the current item in the queue *)
(* is the same as the Head of memory db, if so, the item is taken out of the retry queue and memory db, and added to processed *)
(* list, if not, ConsumeRetryQueueError will be triggered and the item will end up in the end of the queue again *)
ConsumeRetryQueueSucc == retryQueue /= <<>>
                      /\ Head(retryQueue) = Head(memoryDb)
                      /\ processed' = ProcessItem(Head(retryQueue))
                      /\ memoryDb' = Tail(memoryDb)
                      /\ retryQueue' = Tail(retryQueue)
                      /\ UNCHANGED <<currentItem, action, payReportQueue>>
                      
(* We consume messaged from retry queue in parallel, if there is an error, the message goes back to the end of the retry queue *)
ConsumeRetryQueueError == retryQueue /= <<>>
                       /\ retryQueue' = Append(Tail(retryQueue), Head(retryQueue))
                       /\ UNCHANGED <<currentItem, processed, action, memoryDb, payReportQueue>>
                  
(* At any time, the consumer may panic in the middle and restart the process from the beginning *)     
PanicConsumer == action' = "consuming_pay_report"
              /\ UNCHANGED <<currentItem, processed, payReportQueue, memoryDb, retryQueue>>                   

Next == ConsumePayReport
     \/ ConsumePayReportSucc
     \/ ConsumePayReportError
     \/ PutInRetryQueue
     \/ ConsumeRetryQueueSucc
     \/ ConsumeRetryQueueError
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
\* Last modified Thu Feb 03 23:09:43 CET 2022 by rchavesferna
\* Created Thu Feb 03 22:37:38 CET 2022 by rchavesferna
