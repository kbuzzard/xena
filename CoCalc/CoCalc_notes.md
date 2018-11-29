# Setting Lean homework in CoCalc

These are Kevin Buzzard's notes on using Lean to teach a course on CoCalc. Important note: I had paid some money to CoCalc, giving me things like internet access for a project, and the ability to use CoCalc for long enough to compile mathlib without things timing out. YMMV if you haven't done this.

---

I had never used CoCalc before, so first I had to get up to speed with that. I found the tutorial https://tutorial.cocalc.com/ very helpful indeed; this part of the story is not Lean-specific so I won't talk about it here. Note also https://doc.cocalc.com/teaching-create-course.html .

Once I had read this tutorial and set things up, if I logged into CoCalc I could see a "Project" called `M1F` (the name of my course) and within this project I had a file called `M1F_2018.course` which is some sort of course administration file where I can add and delete students and so on. Also within this project I had a directory called "Assignments" which is where I'm going to put the homework. I will refer to me, and this account, as the "instructor" account.

I had also created a fake testing account with a second email address, running in a second browser, just to make sure things worked. I'll call this account the "student" account.

---

Now here is a complete walkthrough of an instructor setting Lean homework to a student. Here are the desiderata.

1) I want to use bleeding-edge mathlib (CoCalc has a mathlib but it's a month or two old, and I am pretty sure that we can't be asking the CoCalc people to keep mathlib up to date with a library that typically gets several commits per week).

2) I also want to use my own library xenalib which has some custom helper functions and theorems (e.g. I want the students to be able to use the fact that for real numbers `x` we have `x^2-3x+2=0` if and only if `x=1` or `x=2`, but they are new undergraduates and have no idea what an integral domain is so are in no position to be able to prove this "math-obvious" fact).

3) I want to be able to set homework in the form of a `.lean` file with some sorries in, and their job is to remove the sorries and get stuff working -- but I want it to *just work* -- I want them to be able to click on the `.lean` file and get started. CoCalc recently added X11 functionality which means that the students could in theory use VS Code but I have not seriously investigated this functionality yet -- if we went down this route then we would have to think about how to get the lean extension installed for the students, and I did not yet invest the time to figure out if this is possible and how to do it.

---

### Creating the homework.

Here I am logged in as the instructor.

Because I want bleeding edge mathlib, I am going to compile mathlib. As the instructor I fire up a terminal in CoCalc, create the directory `~/Assignments/homework01` and make this directory into a lean package with mathlib as a dependency, installed in `~/Assignments/homework01/_target/deps/mathlib` as usual. I change into this directory (and in my case I note that it has the stupid 3.4.1 branch of mathlib so I switch to master with `git checkout master` and then do a `git pull` to sort everything out), and I then compile mathlib with `lean --make`. Of course I guess one could do this on a completely different machine and then move everything over, as long as the project has internet access.

Within `~/Assignments/homework01/src` I put the homework file `question.lean` and I also add a copy of my own little library, in a directory called `xenalib`. Let's say that `xenalib` just contains one file, `xenalib/quadratic.lean` which starts

```lean
import data.real.basic
import tactic.ring

definition quadroots {x : ℝ} : x ^ 2 - 3 * x + 2 = 0 ↔ x = 1 ∨ x = 2 :=
begin
  split,
  { intro H,
etc etc
```

and `question.lean` looks like this:

```lean
import data.real.basic
import xenalib.quadratic

-- fill in the sorry
theorem question_1 : ∃ x : ℝ, x ^ 2 - 3 * x + 2 = 0 := sorry
```

Note that I am doing superfluous imports here -- imports are a problem which needs solving and I am just indicating that they can be solved.

The final thing I need to do to prepare the homework is a kludgy hack which needs to be rethought. I create a file `leanpkg.path.student` in `~/Assignments/homework01/` which looks like this:

```
builtin_path
path /home/user/Assignments/homework01/_target/deps/mathlib/
path /home/user/Assignments/homework01/src/
```

The students are unfortunately going to have to manually copy this file to their home directory; note also that it explicitly mentions the `homework01` directory.

Once mathlib is compiled, this homework is ready to be set.

---

### Enrolling the students

This is not Lean-specific; I open the `M1F_2018.course` file, click on the "Students" tab and enrol the student. Note that in my case, because I paid as the instructor, I have to go to "Configuration" and then "Adjust upgrades" and "Apply changes" to change the "Hosting Type" of the newly-enrolled students from "Free" to "Members-only". By this point, any enrolled student should see a new project, called something like "John Student - M1F 2018-19" (the name of their project will reflect their name and the title of the project, set in the `.course` file). 

---

### Setting the homework

Logged in as the instructor, I just set the homework the way you set CoCalc homework. I open the `M1F_2018.course file`. I click on the "Assignments" tab. I add the assignment. I click on the assignment to open it. And I click on the "Assign" button to assign the project. It takes a few seconds to assign the project, presumably because CoCalc is copying a load of `.olean` files from one place to another.

---

### Doing the homework

Logged in as a student which has been enrolled to the course, I see the project "John Student - M1F 2018-19". If the homework has been assigned to me, within this project there will be an `Assignments/homework01` directory containing an exact copy of the instructor's `Assignments/homework01`. Now here is something I have not yet thought about automating, but which is surely automatable. As the student, I click on New -> Terminal, and I type

```
$ cp Assignments/homework01/leanpkg.path.student .
```

Note that this file itself mentions homework01 (it contains lines such as `path /home/user/Assignments/homework01/src/`), so if you're setting more than one homework you're in trouble here, unless you are sufficiently organised to have your entire library all written by the time you set the first homework. This is a problem with the current set-up. I guess a workaround is to have lots of lines of the form `/home/user/Assignments/homeworkXX/src/` for lots of values of `XX` all contained within this one file.

Now the moment of truth -- the student can click on "Files" then navigate to "Assignments", "homework01", "src" and finally "question.lean". If they click on this, then Lean should start up and *all the imports should work*. They can fill in the sorry with

```lean
import data.real.basic
import xenalib.quadratic

-- fill in the sorry
theorem question_1 : ∃ x : ℝ, x ^ 2 - 3 * x + 2 = 0 :=
begin
  use 1,
  rw quadroots,
  simp,
end
```

Note in particular that they can `use 1` instead of `existsi (1 : ℝ)` because this bleeding edge mathlib tactic, all nicely compiled into bytecode, was sent over as part of the homework, and they can use the `quadroots` function which was defined in `xenalib` -- they have access to this too. 

---

### Issues

The main issue, I guess, is that it would be nicer if the students did not have to open a terminal and copy the file. I guess an `instructions.md` file would be helpful, and if it could tell them to click on something which made the copying happen automatically then this would be great. No doubt this is possible and I guess I could fix up these instructions when I understand how to do this.
