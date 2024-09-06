# Formal RTL Sign-off with Abstract Models

This repository contains the experiments of our work titled "Formal RTL Sign-off with Abstract models".
Our work will be presented and published at the *Design and Verification Conference and Exhibition Europe (DVCon Europe) 2024*.

## Abstract

The complexity of today’s hardware (HW) systems has exhausted the scalability of conventional register transfer level (RTL) design flows. 
The need for more efficient HW design and verification led to the introduction of abstract prototypes at the electronic system level (ESL). 
However, the semantic gap between such untimed ESL models and cycle-accurate RTL designs remains a critical issue, preventing HW sign-off at the higher abstraction layer. 
Existing approaches that aim to bridge this gap are often application-specific or do not establish a formal relationship between the two levels of abstraction. 
The concept of Path Predicate Abstraction (PPA) can establish formal soundness of the abstraction for general-purpose designs, however at the cost of high manual effort.

In this work, we present three techniques to automate large parts of this abstraction technique and its corresponding design methodology. 
We propose a way to generate HW prototypes directly from the abstract model, taking advantage of the strengths of conventional code generation flows. 
Furthermore, we contribute two novel approaches to automate, or even obliterate, the most manually-intensive step of the original abstraction technique. 
We demonstrate the effectiveness of the proposed approaches in several case studies, including industrial designs.
