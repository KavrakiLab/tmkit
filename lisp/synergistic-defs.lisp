(in-package :tmsmt)

(defstruct (syn-container (:include foreign-container)))

(cffi:define-foreign-type syn-handle-t ()
  ()
  (:simple-parser syn-handle-t)
  (:actual-type :pointer))

(defmethod cffi:expand-to-foreign (value (type syn-handle-t))
  `(syn-container-pointer ,value))


(cffi:define-foreign-type in-array-size-t ()
  ()
  (:simple-parser in-array-size-t)
  (:actual-type :pointer))

(defmethod cffi:expand-to-foreign-dyn (value var body (type in-array-size-t))
  (with-gensyms (v i x)
    `(let ((,v ,value))
       (cffi:with-foreign-object (,var 'amino-ffi:size-t (length ,v))
         (let ((,i -1))
           (map nil (lambda (,x)
                      (setf (cffi:mem-aref ,var 'amino-ffi:size-t (incf ,i))
                            ,x))
                ,v))
       ,@body))))
