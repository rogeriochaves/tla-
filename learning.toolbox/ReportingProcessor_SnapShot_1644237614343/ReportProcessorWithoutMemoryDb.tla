-------------------------- MODULE ReportProcessorWithoutMemoryDb --------------------------

EXTENDS Integers, Sequences, TLC, Helpers

VARIABLE payReportQueue, processed, retryQueue, action

PayReportItems == <<1, 2>>

TypeOK == 
  action \in {"consuming_pay_report", "processing_successfull", "put_in_retry_queue"}

Init == payReportQueue = PayReportItems
     /\ processed = <<>>
     /\ retryQueue = <<>>
     /\ action = "consuming_pay_report"
     
(* Function to add the item to the processed list, unless it's already there, simulating idempotency *)
ProcessItem(item) == IF item \notin SeqToSet(processed)
                     THEN Append(processed, item)
                     ELSE processed     

(* When a kafka message is processed succesfully *)
ConsumePayReportSucc == payReportQueue /= <<>>
                     /\ action = "consuming_pay_report"
                     /\ action' = "processing_successfull"
                     /\ processed' = ProcessItem(Head(payReportQueue))
                     /\ UNCHANGED <<payReportQueue, retryQueue>>
                  
(* When a kafka message is processed with error, we put the message in retry queue *)
ConsumePayReportError == payReportQueue /= <<>>
                      /\ action = "consuming_pay_report"
                      /\ action' = "put_in_retry_queue"
                      /\ retryQueue' = Append(retryQueue, Head(payReportQueue))
                      /\ UNCHANGED <<processed, payReportQueue>>
     
(* We commit to kafka either after message is processed successfully OR after is had been put on the retry queue *)
CommitToPayReport == (action = "processing_successfull" \/ action = "put_in_retry_queue")
                  /\ payReportQueue' = Tail(payReportQueue)
                  /\ action' = "consuming_pay_report"
                  /\ UNCHANGED <<processed, retryQueue>>

(* We consume messaged from retry queue in parallel, if sucessfully, they are taken out of the retry queue, and added to processed list *)
ConsumeRetryQueueSucc == retryQueue /= <<>>
                      /\ processed' = ProcessItem(Head(retryQueue))
                      /\ retryQueue' = Tail(retryQueue)
                      /\ UNCHANGED <<action, payReportQueue>>
                      
(* We consume messaged from retry queue in parallel, if there is an error, the message goes back to the end of the retry queue *)
ConsumeRetryQueueError == retryQueue /= <<>>
                       /\ retryQueue' = Append(Tail(retryQueue), Head(retryQueue))
                       /\ UNCHANGED <<processed, action, payReportQueue>>

(* At any time, the consumer may panic in the middle and restart the process from the beginning *)     
PanicConsumer == action' = "consuming_pay_report"
              /\ UNCHANGED <<processed, payReportQueue, retryQueue>> 

Next == ConsumePayReportSucc
     \/ ConsumePayReportError
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
\* Last modified Thu Feb 03 23:27:32 CET 2022 by rchavesferna
\* Created Thu Feb 03 19:11:04 CET 2022 by rchavesferna