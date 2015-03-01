(in-package :tmsmt)

(defun load-sexp (filename)
  "Read a single s-expression from a file"
  (with-open-file (s filename :direction :input)
    (read s)))

(defun check-symbol (value required)
  "Check symbol name of `VALUE' is string= to symbol name of `REQUIRED'"
  (unless (string= (string value) (string required))
    (error "Symbol mismatch on ~A, required ~A" value required)))

(declaim (inline fold))
(defun fold (function initial-value sequence &rest more-sequences)
  (apply #'sycamore::fold function initial-value sequence more-sequences))

(defmacro or-compare-2 (compare-exp-1 compare-exp-2)
  "Short-circuit evaluatation of arguments, returning the first one that is nonzero."
  (alexandria:with-gensyms (sym1)
   `(let ((,sym1 ,compare-exp-1))
      (declare (fixnum ,sym1))
      (if (zerop ,sym1)
          ,compare-exp-2
          ,sym1))))

(defmacro or-compare (&rest vals)
  "Short-circuit evaluatation of arguments, returning the first one that is nonzero."
  (cond
    ((null vals) 0)
    ((null (cdr vals)) (car vals))
    (t `(or-compare-2 ,(car vals)
                      (or-compare ,@(cdr vals))))))

(defun string-compare (a b)
  (declare (type string a b))
  (labels ((helper (a b)
             (loop
                for x across a
                for y across b
                while (eql x y)
                finally (return (- (char-code x) (char-code y))))))

    (etypecase a
      (simple-string
       (etypecase b
         (simple-string (helper a b))
         (string (helper a b))))
      (string (helper a b)))))

(defun bit-vector-compare (a b)
  "Compare bitvectors `A' and `B'."
  (declare (type simple-bit-vector a b)
           (optimize (speed 3) (safety 0)))
  (let* ((n-a (length a))
         (n-b (length b)))
    (or-compare (fixnum-compare n-a n-b)
                (let ((i (mismatch a b)))
                  (if i
                      (let ((x (aref a i))
                            (y (aref b i)))
                        (- x y))
                      0)))))

(defun fixnum-compare (a b)
  "Compare two fixnums"
  (declare (type fixnum a b))
  (cond ((< a b) -1)
        ((> a b) 1)
        (t 0)))

(defun gsymbol-compare-atom (a b)
  (declare (optimize (speed 3) (safety 0)))
  (if (eq a b)
      0
      (etypecase a
    (fixnum
     (etypecase b
       (fixnum (if (< a b) -1 1))
       (character 1)
       (string 1)
       (symbol 1)))
    (character
     (etypecase b
       (fixnum -1)
       (character (if (< (char-code a) (char-code b))
                      -1 1))
       (string 1)
       (symbol 1)))
    (string
     (etypecase b
       (fixnum -1)
       (character -1)
       (string (string-compare a b))
       (symbol 1)))
    (symbol
     (etypecase b
       (fixnum -1)
       (character -1)
       (string -1)
       (symbol (cond ((string< a b) -1)
                     ((string> a b) 1)
                     (t 0))))))))

(defun gsymbol-compare (a b)
  (etypecase a
    (null (if b -1 0))
    (atom (etypecase b
            (null 1)
            (atom (gsymbol-compare-atom a b))
            (list -1)))
    (cons
     (etypecase b
       (atom 1)
       (list (or-compare (gsymbol-compare (car a) (car b))
                         (gsymbol-compare (cdr a) (cdr b))))))))
