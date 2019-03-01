Contributing
============

`develop`: development happens here; submit PRs from other branches to this branch

`master` : contains versioned releases that can be referenced from other repos

Workflow
--------

We maintain all work items in Github issues arranged in milestones. 
We use `ZenHub` to track the progress of the milestone epics/issues and they can be seen on the `ZenHub` board.

New work items are selected when an issues/epic is completed into the *Backlog* column of the kanban board. 
These are the items that following the grand plan will be worked on during the current week.

```
|************| |*********| |*************| |***************| |***************|
| New Issues | | Backlog | | In Progress | |   Review/QA   | |  Done/Closed  |
|------------| |---------| |-------------| |---------------| |---------------|
|            | |         | |             | |               | |               |
|    ...    ---->   ...  --->    ...    ---->     ...     ---->      ...     |
|____________| |_________| |_____________| |_______________| |_______________|
```

Submitting PRs
--------------

Pull requests should be opened against `develop`.

Please describe the PR in as much detail as would be necessary to understand the code changes, and make sure the description is consistent with the changes introduced.
The PR should contain a link to the issue, any comment regarding something specific about the PR, it should pass the CI.
After the PR is submitted, you need to ping the squad lead for a review (while also removing "WIP" tag if present).

If there is any confusion or if somebody is blocked, they should reach out to the squad lead.

