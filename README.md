JMLCute
=======

JMLCute uses jCUTE's Concolic engine and AspectJML's JML compiler to generate JUnit Test Cases for a project given the project's source code and its JML specifications.

Build
-----
You need Vagrant or a 64-bit Linux system to run jmlcute.

If you have Vagrant, run 'vagrant up' to build the system.
Then, run 'vagrant ssh' followed by 'cd /vagrant/' to change to the current synced directory within the virtual 64-bit Linux environment. Any changes to the virtual (guest) directory will be felt in the host. To exit the virtual environment run 'exit'.

If you run jmlcute-essentials in a 64-bit Linux system, jmlcute is already built.

Run
---
To run jmlcute on the project within src/main/java, run './debugJMLCute'.

Help
----
If you find a bug or cannot build or run this project, please contact one of the contributors.

