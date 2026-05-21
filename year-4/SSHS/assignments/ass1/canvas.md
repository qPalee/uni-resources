# Summary of assignment

A new employee at EvilCorp believes firmly in new technologies, and now uses ChatGPT to create their programs. You are hired as external consultant and need to demonstrate that this leads to security issues! To do so, you must write a fuzzing harness, find vulnerabilities, and write a report about your findings.
Assignment

You are in the role of a external cybersecurity consultant. You are given a set of files to carry out your evaluation. You will need to perform three groups of tasks: fuzzing, vulnerability analysis, patching, and reporting. You can download the analysis template from: assignment1.zip Download assignment1.zip.

Your goals are as follows:

Part 1: Fuzzing

    In a directory called "fuzz", complete the template docker file to:
        Install relevant software for compiling the fuzzing target;
        Clone, build and install the AFL++ fuzzer (https://github.com/AFLplusplus/AFLplusplus);
        Compile the target "js.c" inside the container for fuzzing with AFL++;
    Edit the "run.sh" launcher to start fuzzing automatically on container launch.
    Modify in/seed to contain a suitable seed for the target.

Part 2: Vulnerability analysis and patching

Then, in a directory called "fixed":

    Select one of the AFL++ generated crashes to further investigate:
    Identify the root cause of the crash, e.g., using source file, address sanitizer, gdb.
    Prepare a file named "js.patch" containing a correctly formatted patch which fixes the bug leading to the crash. If you are unsure on what a valid patch looks like, consult the "patch(1)" manual page by running "man patch". We will only consider patches understood by the "patch" tool to be valid and you will lose marks for any other format.
    Create a Dockerfile named "Dockerfile" and a launcher "run.sh" that will build and run this docker file (using the initial files as examples) to automatically apply the patch, and demonstrate the validity of the fix.

Part 3: Reporting

    Write a correctly formated CVE report in a "CVE-YYYY-NNNNN.txt" file (replace YYYY and NNNNN with suitable values). Use tools such as (https://nvd.nist.gov/vuln-metrics/cvss/v3-calculator Links to an external site.) to compute the CVSS metrics. Define a adequate CPE identifier assuming the name of the target is "evilcorp_js v0.1.2.1".
    Write vulnerability report of up to 2 pages, in PDF format (e.g., report-teamXX.pdf), detailing your findings including: vulnerability details, root cause analysis, reasoning behind the suggested patch.

