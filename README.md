JMLCute
=======

JMLCute uses jCUTE's Concolic engine and AspectJML's JML compiler to generate JUnit Test Cases for a project given the project's source code and its JML specifications.

Build
-----
You need Vagrant or a 64-bit Linux system to run jmlcute.

If you have Vagrant, run 'vagrant up' to build the system, followed by 'vagrant ssh' to access the 64-bit Linux virtual environment.
To exit the virtual environment run 'exit'.

Building the system the first time may take up to one hour. Subsequent builds will be much faster (less than a minute).

When inside the virtual environment, the /vagrant directory will be synced with this project, so any changes to the /vagrant directory will be felt in the host.

If you have a 64-bit Linux system, then jmlcute is already built.

Run
---
To run jmlcute over the project within src/main/java, run './runjmlcute TestDoubleRecursion'.

Help
----
If you find a bug or cannot build or run this project, please contact one of the contributors.

