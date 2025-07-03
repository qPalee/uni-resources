# Activity Plan for Week 10

### Attend the lab on Monday 11-2pm
 * *The first two hours are mandatory, but UGTAS will still be available during the third hour.*
 * Work on the [Lab 10 exercises](/files/LectureNotes/files/exercises/lab10.lagda.md) and feel free to ask for help from the module team.

### Attend the lectures on Tuesday 11:00-13:00 and Wednesday 11:00-12:00

### This week we will do **revision** using Dijkstra's Algorithm

We will start from the [Wikipedia page on Dijkstra's algorithm](https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm) for computing shortest paths in graphs.

I will begin by pointing out that there are many imprecisions in that Wikipedia page. You will help me to fix these imprecisions based on what you have learned in this module.

The idea of the lectures for this week is *not* to produce a full implementation and proof of Dijkstra's algorithm, but *instead* to apply what you have learned so far to both detect imprecisions and fix them.

In particular, we will take the opportunity to consider two things used in Dijkstra's algorithm:

1. The extension of the natural numbers with a point at infinity, including addition and order.

1. The definition of a type of priority queues using a record. You will notice how imprecise the definitions are in most of the literature. We will try to make them more precise during the lectures.

1. The formulation of the invariant condition used to prove the correctness of Disjktra's algorithm.

We are likely not to be able to complete Dijkstra's algorithm in just a week, but this is fine. The important thing is to use what you have learned in this module to try to make as much progress together in the lectures as we can, for the sake of revision.

The main points are

* how do we say, precisely, that a program does?
* how do we argue that what we say is what the program really does?
