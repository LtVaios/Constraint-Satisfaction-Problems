# Radio Link Frequency Assignment Problem (RLFAP)
✔️ Solving the famous radio link frequency assignment problem (RLFA) by implementing various contraint satisfaction algorithms like fc, mac, fc-cbj and min-con while using the dom/wdeg heuristic. More info about the project and how the dataset files work you can find at: https://miat.inrae.fr/schiex/rlfap.shtml#intro

## Installation / Run
🔨 Download and install the files locally. <br /><br />
🔁 To run the code simply type: 
  ```
  $ python csp.py
  ```
This command will run the project with a default data file from the dataset and fc algorithm. If you want to change the data file you must go in csp.py (lines 708-710) and write the appropriate var,dom and ctr files associated with the problem you want the project to run on. Below that there are some commented code section each one for a specific algorithm so if you want to change the algorithm used you must uncomment the section for the algorithm you want (there are comment guidlines for each algorithm section) and comment the other ones.
<br /><br />
📝You can also find a table with the statistics of each algorithm in the report and some code insights in Greek. <br \>

## Constraint Satisfaction Algorithms
🔸 FC (forward checking) algorithm:  Forward checking is the easiest way to prevent future conflicts. Instead of performing arc consistency to the instantiated variables, it performs restricted form of arc consistency to the not yet instantiated variables. We speak about restricted arc consistency because forward checking checks only the constraints between the current variable and the future variables. When a value is assigned to the current variable, any value in the domain of a "future" variable which conflicts with this assignment is (temporarily) removed from the domain. The advantage of this is that if the domain of a future variable becomes empty, it is known immediately that the current partial solution is inconsistent. Forward checking therefore allows branches of the search tree that will lead to failure to be pruned earlier than with simple backtracking. Note that whenever a new variable is considered, all its remaining values are guaranteed to be consistent with the past variables, so the checking an assignment against the past assignments is no longer necessary.<br /><br />
🔸 Mac (Maintaining arc consistency): MAC is also a check forward algorithm, it works mainly in the same maner as
FC. However it does full arc consistency check over each future nodes, which it
also checks the future variables against each other removing any arc-inconsistent
value from their domains. It does additional forward consistent checking.<br /><br />
🔸 FC-CBJ (Conflict Directed Backjumping): CBJ maintains a jumpback set J for each variable x. CBJ also adds earlier, instantiated variables to Ji. Upon reaching a dead-end at xi, the algorithm jumps back to the latest variable in Ji.<br /><br />
🔸 Min-Con (minimum conflicts): https://en.wikipedia.org/wiki/Min-conflicts_algorithm.<br /><br />
📝 PS: For this project I implemented dom/wdeg heuristic to use for my algorithms. More info about this heuristic you can find in this paper: http://www.frontiersinai.com/ecai/ecai2004/ecai04/pdf/p0146.pdf.

## Built with
<img src="https://upload.wikimedia.org/wikipedia/commons/thumb/c/c3/Python-logo-notext.svg/110px-Python-logo-notext.svg.png" alt="MarineGEO circle logo" style="height: 100px; width:100px;"/>
