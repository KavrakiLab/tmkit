(in-package :tmsmt)



;;; Load Library ;;;

(cffi:define-foreign-library libtmsmt
  (:unix (:or "libtmsmt.so"
              (:default "libtmsmt")))
  (t (:default "libtmsmt")))


(cffi:use-foreign-library libtmsmt)

;;; Bind Functions ;;;
(cffi:defcfun tmplan-parse-filename :pointer
  (filename :string)
  (region :pointer))


(cffi:defcfun tmplan-map-ops :int
  (tmp :pointer)
  (function :pointer)
  (context :pointer))

(cffi:defcfun tmplan-op-type op-type
  (tmplan :pointer))

(cffi:defcfun tmplan-op-action-get :string
  (op :pointer))

(cffi:defcfun tmplan-op-motion-plan-map-var :int
  (op :pointer)
  (function :pointer)
  (context :pointer))

(cffi:defcfun tmplan-op-reparent-get-frame :string
  (op :pointer))

(cffi:defcfun tmplan-op-reparent-get-new-parent :string
  (op :pointer))

;;; Wrappers ;;;

(defvar *plan-ops*)
(defvar *plan-config-names*)

(defgeneric translate-op (type pointer))

(defmethod translate-op ((type (eql :action)) pointer)
  (declare (ignore type))
  (tm-op-action (tmplan-op-action-get pointer)
                nil nil))

(cffi:defcallback fetch-var :void
    ((context :pointer) (name :pointer))
  (declare (ignore context))
  (push (cffi:foreign-string-to-lisp name)
        *plan-config-names*))

(defmethod translate-op ((type (eql :motion-plan)) pointer)
  (declare (ignore type))
  (let ((*plan-config-names* nil))
    (tmplan-op-motion-plan-map-var pointer
                                   (cffi:callback fetch-var)
                                   (cffi:null-pointer))
    ;;(print (reverse *plan-config-names*))
    (robray::make-motion-plan)))

(defmethod translate-op ((type (eql :reparent)) pointer)
  (declare (ignore type))
  (list 'tm-op-reparent nil
        (tmplan-op-reparent-get-frame pointer)
        (tmplan-op-reparent-get-new-parent pointer)))


(cffi:defcallback translate-plan-op :void
    ((context :pointer) (op :pointer))
  (declare (ignore context))
  (let ((type (tmplan-op-type op)))
    (push (translate-op type op)
          *plan-ops*)))



(defun translate-tmplan (pointer)
  (let ((*plan-ops* nil))
    (tmplan-map-ops pointer
                    (cffi:callback translate-plan-op)
                    (cffi:null-pointer))
    (reverse *plan-ops*)))

(defun parse-tmplan (pathname)
  ;; Parse pathname using the thread-local memory region
  (let ((ptr (tmplan-parse-filename (rope-string (rope pathname))
                                    (cffi:null-pointer))))
    (if (cffi:null-pointer-p ptr)
        (error "Could not parse plan file `~A'." pathname)
        (unwind-protect
             (translate-tmplan ptr)
          (amino::aa-mem-region-local-pop ptr)))))
