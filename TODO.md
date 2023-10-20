I want to rerun the experiments, 
but with progress tracking for timeout and oom.
The points to update progress are:
* Preprocessing - V
* Prove base - V
* equiv_reduc - each iteration for now - V
* case_split - start - V
* case_split - equiv_reduc - V
* case_split - find splitters - V
* case_split - merge conclusions - V
* Prover constructor in ind - V
* Finished - V

At each check point I want to dump the following stats:
* split count - V
* graph size - V
* time - V
* matches - V
* applications - V

A good way to dump this would probably be to a file I continuously update.