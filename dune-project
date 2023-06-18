(lang dune 3.6)
(using coq 0.6)
(name coq-mu-mu-t)

(license "GPLv3")
(authors "Peio Borthelle")
(maintainers "Peio Borthelle")
(source (github lapin0t/mu-mu-tilde))
(bug_reports "https://github.com/lapin0t/mu-mu-tilde/issues")

(generate_opam_files true)

(package
 (name coq-mu-mu-t)
 (synopsis "A formalization of the mu-mu-tilde language and some classical realizability.")
 (version 0.1)
 (depends
  (coq (>= 8.16))
  (coq-equations (>= 1.3))
 )
)
