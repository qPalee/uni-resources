# Summary of assignment

After showing your skills in security via automation, fuzzing, and vulnerability reporting, EvilCorp has a new task for you: Help them to recover key information about their legacy hardware security token, hosted on the raspberry Pi Pico!

Unfortunately, the engineer who originally created the token left the company and documentation is missing. You will need to probe the different communication interface and recover the Pin code to unlock the device. For this assignment, you will receive hardware (1 set per group). Please make sure to return this after you finished the assignment.

 
Assignment

You are in the role of a external cybersecurity consultant and your assignment is divided in two parts: protocol reverse engineering and rehosting.
Please refer to the assignment introduction slides [link] or recording for additional information on the hardware. For part 2, you are also given a set of files to carry out your task: assignment2.zip Download assignment2.zip.

 

Part 1: Protocol Reverse Engineering

Notes: Throughout this assignment, you are asked to retrieve different "flags". In this assignment, these are human-readable strings, following the format `sshs{$random_string}`. Please include the retrieved flags in your submission.

 

Goals:

    Preparation:
        Obtain the set of hardware from the lecturers or TAs (1 set per group)
        Flash the target firmware on the device
        Download the saleae Logic 2 software for your operation system: https://www.saleae.com/pages/downloads Links to an external site.
        Make sure you can communicate with your Raspberry Pi Pico via USB, using for instance minicom on Mac/Linux or Putty on Windows.
    UART identification:
        Use the menu of the pico firmware to send a message via UART. The message is sent once every time the menu entry is selected.
        Attach the logic analyzer to the right Pins and capture the traffic using the Logic 2 software
        Decode the UART message using the corresponding protocol decoder with the right parameters.
    SPI identification:
        Use the menu of the pico firmware to send a message via SPI. The message is sent once every time the menu entry is selected.
        Probe different pins with the logic analyzer to find the pins on which the message is transmitted.
        Decode the SPI message using the corresponding protocol decoder with the right parameters.

Hints:

    If you are stuck connecting to your Pico, a look at the Raspberry Pi Pico getting started guide Links to an external site. may help.
    When connected to the Pico and not seeing any output, try typing a number and enter.
    The Logic 2 software has some nice features that can help you inspect signals and even decode them.
    If you observe framing errors, your UART decoder settings are not 100% correct. Try looking at the signal (and the lecture slides) and figure out why you encounter these errors.
    The SPI signal in this exercise uses 4 wires.
    If the Logic 2 tool reports that it cannot keep up with the selected sample rate, consider reducing the sample rate.
    Each pin has a limited set of functions it can be used for: find the data sheet for the raspberry pi pico check the pinout carefully.

 

Part 2:  Rehosting

Note: For this part of the assignment, you receive a dump from the raspberry pi Pico, at the entry point of the function `assignment_2B_rehost`. This dump contains: the register state (`regs.txt`), the content of the firmware in flash memory (`fw.bin`), the ROM memory of the raspberry pi pico (`rom.bin`) and its content on RAM (`sram.bin`). Additionally, you receive `sshs.elf`, a compiled version of the firmware with symbols. You can load this file in Ghidra to aid your reverse engineering during this assignment.

Goals:

    Create a Dockerfile which copies over the provided files and sets up unicorn and all its dependencies
    Rehost the function `assignment_2B_rehost` using unicorn and retrieve the pin:
        Initialize Unicorn, including register state and memory regions
        Identify functions which need to be skipped and create according hooks
        Identify functions for output and provide according hooks
        Identify the function reading the input and provide a hook writing the input to the right location in memory
        Execute your rehosted function in a loop, using a different guess for the Pin on each iteration. If guessed successful, you will see the flag in the output

Hints:

    You can choose a language of your choice for interacting with Unicorn. We recommend using Python though; Unicorn for Python can be set up using `python3 -m pip install unicorn`, assuming all dependencies for this have been installed
    Unicorn include samples which can be used as reference. For Python, you can for instance use test_arm.py Links to an external site. as basis for your rehosting script. 
    To skip a full function, you can create a code hook at the entry point of the function. Then, write the contents of the link register to the program counter register and exit your hook
    The valid PIN is in the range [0,9999]
    Having problems to kick-off emulation? Make sure your addresses include the Thumb bit!
    Try to make your rehosting efficient - you can install hooks on specific addresses; a global hook called for every basic b[118;1:3ulocks will provide a performance penalty!
    Do not try to reverse engineer the `decrypt_rehosting_flag` function. Let the rehosting do the work for you. :)

Deliverables:

    A brief PDF report (max 2 pages) containing:
        The 3 flags
        A screenshot containing the correct UART setting
        A screenshot containing the correct SPI setting
        A textual explanation on how you managed to find the UART settings.
        A textual explanation on how you managed to find the pins and the SPI settings
        A textual explanation of the functions you had to hook/intercept to solve the rehosting challenge
    Your rehosting script and auxiliary files it relies on
    A Dockerfile and a run.sh to execute your rehosting script

