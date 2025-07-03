# Test 1

## Marking table

The exercises are defined so that it is hard to get a first-class mark.

| Mark         | Cut-off            |
| ------------ | ------------------ |
| 1st          | 28 marks and above |
| upper second | 24-27 marks        |
| lower second | 20-23 marks        |
| third        | 16-19 marks        |
| fail         | 0-15 marks         |

All questions have equal weight, with eight marks each, with a total of 40
marks.

## Preparation

* The test must be completed on JupyterLab.
* Run `git pull` on JupyterLab to make sure you have the latest version of the
  course repository.
* We have defined some helper functions for your in the `Types.hs` file. You are
  encouraged to make use of them in your solutions.
* Do __not__ modify either the file `Types.hs` or the file
  `Test1-Template.hs`.
* Copy the file `Test1-Template.hs` to a new file called
  `Test1.hs` and write your solutions in `Test1.hs`.

  __Don't change the header of this file, including the module declaration, and,
  moreover, don't change the type signature of any of the given functions for
  you to complete.__

  __If you do make changes, then we will not be able to mark your submission and
  hence it will receive zero marks!__
* Solve the exercises below in the file `Test1.hs`.

## Submission procedure

* If your submission doesn't compile or fails to pass the presubmit script on
  JupyterLab, it will get zero marks.
* Run the presubmit script provided to you on your submission from Jupyter by
  running `./presubmit.sh Test1` in the terminal (in the same folder as
  your submission).
* This will check that your submission is in the correct format.
* If it is, submit it on Canvas.
* Otherwise fix and repeat the presubmission procedure.

## Plagiarism

Plagiarism will not be tolerated. Copying and contract cheating have led to full
loss of marks, and even module or degree failure, in the past.

You will need to sign a declaration on Canvas, before submission, that you
understand the [rules](/README.md#plagiarism) and are abiding by them, in order
for your submission to qualify.

## Background material

- Each question has some **Background Material**, an **Implementation Task** and
  possibly some **Examples**.
- Read this material first, then implement the requested function.
- The corresponding type appears in the file `Test1-Template.hs` (to be
  copied by you).
- Replace the default function implementation of `undefined` with your own
  function.

## More Rules

* This is an open book test.
* You may consult your own notes, the course materials, any of the recommended
  books or [Hoogle](https://hoogle.haskell.org/).
* Feel free to write helper functions whenever convenient.
* All the exercises may be solved without importing additional modules. Do not
  import any modules, as it may interfere with the marking.

## Submission Deadline

* The official submission deadline is 1pm.
* If you are provided extra time by the Welfare office then your submission
  deadline is 1:30pm or 2:00pm.
* Submissions close 10 minutes after your deadline, and late submissions have 5%
  penalty

## Question 1 — Even majority (**8 marks**)

**Task** Write the following function `evenMajority`, that takes a list of
integers, and tells whether more than half of them are even.

```haskell
evenMajority :: [Int] -> Bool
evenMajority ns = undefined
```

## Question 2 — 5-smooth numbers (**8 marks**)

A 5-smooth number is an integer which has no prime factor larger than 5. For an
integer N, we define S(N) as the set of 5-smooth numbers less than or equal to
N. For example S(20) = {1,2,3,4,5,6,8,9,10,12,15,16,18,20}

**Task** Define the following function `get5SmoothNumbers`, that gives a list of
all 5-smooth numbers less than or equal to a given number.

```haskell
get5SmoothNumbers :: Int -> [Int]
get5SmoothNumbers k = undefined
```

Examples:

```hs
*Test1> get5SmoothNumbers 25
[1,2,3,4,5,6,8,9,10,12,15,16,18,20,24,25]

*Test1> get5SmoothNumbers 50
[1,2,3,4,5,6,8,9,10,12,15,16,18,20,24,25,27,30,32,36,40,45,48,50]
```

## Question 3 — Train stops (**8 marks**)

Consider the following type of train stops on the West Midlands Railway line,
from Redditch to Birmingham New Street.

```haskell
data TrainStop = BirminghamNewStreet
               | FiveWays
               | University
               | SellyOak
               | Bournville
               | KingsNorton
               | Northfield
               | Longbridge
               | BarntGreen
               | Alvechurch
               | Redditch
               deriving (Eq, Show)
```

We define the function `theStopAfter` on this type, which encodes the
information of which stop comes immediately after which stop.

```haskell
theStopAfter :: TrainStop -> TrainStop
theStopAfter Redditch            = Alvechurch
theStopAfter Alvechurch          = BarntGreen
theStopAfter BarntGreen          = Longbridge
theStopAfter Longbridge          = Northfield
theStopAfter Northfield          = KingsNorton
theStopAfter KingsNorton         = Bournville
theStopAfter Bournville          = SellyOak
theStopAfter SellyOak            = University
theStopAfter University          = FiveWays
theStopAfter FiveWays            = BirminghamNewStreet
theStopAfter BirminghamNewStreet = undefined
```

Note that the function is undefined on `BirminghamNewStreet` because that is the
last possible stop on this line. You should ensure that this function is never
called on `BirminghamNewStreet`, because the program will crash if you do that.

**Task** Define the following function `comesBefore`, using the given
`theStopAfter` function, such that `comesBefore s1 s2` is `True` if and only if
`s1` is a stop preceding stop `s2`.

```haskell
comesBefore :: TrainStop -> TrainStop -> Bool
comesBefore s1 s2 = undefined
```

Some examples:

```hs
*Test1> comesBefore University BirminghamNewStreet
True
*Test1> comesBefore Bournville FiveWays
True
*Test1> comesBefore BirminghamNewStreet University
False
*Test1> comesBefore University KingsNorton
False
*Test1> comesBefore University University
False
```

## Question 4 — Repeated applications of a function (**8 marks**)

**Task** Write a function `countApplications`

```haskell
countApplications :: (a -> a) -> (a -> Bool) -> a -> Int
countApplications f p x = undefined
```

that takes

  1. a function `f :: a -> a`,
  1. a termination condition `p :: a -> Bool`, and
  1. an input `x :: a`,

and counts the number of times that the function `f` must be repeatedly applied
to `x` until the output satisfies the condition `p`.

Here is an example of how to use this function:

```hs
*Test1> countApplications (\n -> n `div` 2) odd 8
3
*Test1> countApplications (\n -> n `div` 2) odd 10
1
```

We will only test your implementation of `countApplications` on functions that
do terminate with respect to the termination condition.

## Question 5 — Higher order functions (**8 marks**)

**Task** Write a function `f` of the following type

```haskell
f :: (a -> a -> r) -> ((a -> r) -> a) -> r
f g h = undefined
```

The function should terminate for all terminating inputs. Your solution should
not use recursion or `undefined`.
