(in-package :tmsmt)




(defmacro with-deferred-signals (&body body)
  `(progn
     (sb-thread::block-deferrable-signals)
     (unwind-protect (progn ,@body)
       (sb-unix::unblock-deferrable-signals))))



;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; FOREIGN CONTAINERS ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;


;;; Wrapper for a foreign pointer.
;;; Used to call destructor when GC'ed

(defstruct foreign-container
  pointer)


(defun foreign-container-finalizer (object destructor)
  "Register finalizer to call DESTRUCTOR on OBJECT's pointer.
RETURNS: OBJECT"
  (let ((pointer (foreign-container-pointer object)))
    (sb-ext:finalize object (lambda () (funcall destructor pointer))))
  object)



;;;;;;;;;;;;;;;;;;
;; NODE HANDLE ;;;
;;;;;;;;;;;;;;;;;;
(defstruct (node-handle (:include foreign-container)
                        (:constructor make-node-handle (pointer))))


;;;;;;;;;;;;;;;;;;;;;;;;
;;; MOVEIT CONTAINER ;;;
;;;;;;;;;;;;;;;;;;;;;;;;

(defstruct (moveit-container (:include foreign-container)
                             (:constructor make-moveit-container (pointer)))
  (relative-tf-tree (make-tf-tree)))

(cffi:define-foreign-type moveit-container-t ()
  ()
  (:simple-parser moveit-container-t)
  (:actual-type :pointer))

(defmethod cffi:expand-to-foreign (value (type moveit-container-t))
  `(moveit-container-pointer ,value))

(defun container-add-object (container parent relative-tf name)
  "Add object to container. Return absolute transform."
  ;; Add relative to tree
  (setf (moveit-container-relative-tf-tree container)
        (tf-tree-insert (moveit-container-relative-tf-tree container)
                        (tf-tag parent relative-tf name)))
  ;; Find absolute
  (tf-tag-tf (tf-tree-absolute-tf (moveit-container-relative-tf-tree container)
                                 name)))

(defun container-remove-object (container frame)
  (setf (moveit-container-relative-tf-tree container)
        (tf-tree-remove (moveit-container-relative-tf-tree container)
                        frame)))

(defun container-remove-all-objects (container)
  (setf (moveit-container-relative-tf-tree container)
        (make-tf-tree)))
