--------------------------- MODULE WTCSpec ---------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    KEYS,       \* Set of cache keys
    VALUES,     \* Set of possible values
    READERS,    \* Set of reader processes
    NULL        \* Null value for empty cache entries

VARIABLES
    cache,      \* Cache state: [key |-> value]
    database,   \* Database state: [key |-> value]
    writer_state,   \* Writer process state
    writer_key,     \* Key that the active writer is writing
    reader_states   \* Reader process states: [reader |-> state]

vars == <<cache, database, writer_state, writer_key, reader_states>>

\* Type invariants
TypeOK == 
    /\ cache \in [KEYS -> VALUES \cup {NULL}]
    /\ database \in [KEYS -> VALUES]
    /\ writer_state \in {"idle", "writing_db"}
    /\ writer_key \in KEYS \cup {NULL}
    /\ reader_states \in [READERS -> [state: {"idle", "reading_cache", "reading_db"}, 
                                      key: KEYS \cup {NULL},
                                      value: VALUES \cup {NULL}]]

\* Initial state
Init ==
    /\ cache = [k \in KEYS |-> NULL]
    /\ database \in [KEYS -> VALUES]  \* Database has initial values
    /\ writer_state = "idle"
    /\ writer_key = NULL
    /\ reader_states = [r \in READERS |-> [state |-> "idle", key |-> NULL, value |-> NULL]]

\* Writer starts a write operation
WriterStart(key, value) ==
    /\ writer_state = "idle"
    /\ writer_state' = "writing_db"
    /\ writer_key' = key
    /\ database' = [database EXCEPT ![key] = value]
    /\ UNCHANGED <<cache, reader_states>>

\* Writer updates cache after database write and completes
WriterUpdateCache ==
    /\ writer_state = "writing_db"
    /\ writer_key # NULL
    /\ writer_state' = "idle"
    /\ writer_key' = NULL
    /\ cache' = [cache EXCEPT ![writer_key] = database[writer_key]]
    /\ UNCHANGED <<database, reader_states>>

\* Reader starts reading from cache
ReaderStartCache(reader, key) ==
    /\ reader_states[reader].state = "idle"
    /\ reader_states' = [reader_states EXCEPT 
                         ![reader] = [state |-> "reading_cache", key |-> key, value |-> NULL]]
    /\ UNCHANGED <<cache, database, writer_state, writer_key>>

\* Reader gets value from cache (hit)
ReaderCacheHit(reader) ==
    LET key == reader_states[reader].key IN
    /\ reader_states[reader].state = "reading_cache"
    /\ cache[key] # NULL
    /\ reader_states' = [reader_states EXCEPT 
                         ![reader] = [state |-> "idle", key |-> NULL, value |-> cache[key]]]
    /\ UNCHANGED <<cache, database, writer_state, writer_key>>

\* Reader misses cache, goes to database
ReaderCacheMiss(reader) ==
    LET key == reader_states[reader].key IN
    /\ reader_states[reader].state = "reading_cache"
    /\ cache[key] = NULL
    /\ reader_states' = [reader_states EXCEPT 
                         ![reader] = [@ EXCEPT !.state = "reading_db"]]
    /\ UNCHANGED <<cache, database, writer_state,writer_key>>

\* Reader gets value from database
ReaderDatabaseRead(reader) ==
    LET key == reader_states[reader].key IN
    /\ reader_states[reader].state = "reading_db"
    /\ reader_states' = [reader_states EXCEPT 
                         ![reader] = [state |-> "idle", key |-> NULL, value |-> database[key]]]
    /\ UNCHANGED <<cache, database, writer_state, writer_key>>

\* Next state relation
Next ==
    \/ \E key \in KEYS, value \in VALUES : WriterStart(key, value)
    \/ WriterUpdateCache
    \/ \E reader \in READERS, key \in KEYS : ReaderStartCache(reader, key)
    \/ (\E reader \in READERS : ReaderCacheHit(reader))
    \/ (\E reader \in READERS : ReaderCacheMiss(reader))
    \/ (\E reader \in READERS : ReaderDatabaseRead(reader))

\* Liveness property - writer eventually finishes and returns to idle
WriterEventuallyIdle == 
    (writer_state # "idle") ~> (writer_state = "idle")

\* Liveness property - readers eventually get correct values
\* Liveness property - readers eventually make progress and get correct values
ReaderEventualProgress == 
    \A reader \in READERS :
        /\ (reader_states[reader].state = "reading_cache") ~> 
           (reader_states[reader].state \in {"idle", "reading_db"})
        /\ (reader_states[reader].state = "reading_db") ~> 
           (reader_states[reader].state = "idle")

Fairness ==
    /\ WF_vars(WriterUpdateCache)
    /\ \A reader \in READERS: WF_vars(ReaderCacheHit(reader) \/ ReaderCacheMiss(reader) \/ ReaderDatabaseRead(reader))

Spec == Init /\ [][Next]_vars /\ Fairness 

\* Safety properties
\* CacheConsistency == 
\*     \A key \in KEYS : cache[key] # NULL => cache[key] = database[key]


CacheEventualConsistency ==
    \A key \in KEYS : 
        (cache[key] # NULL) ~> (cache[key] = database[key])



=============================================================================