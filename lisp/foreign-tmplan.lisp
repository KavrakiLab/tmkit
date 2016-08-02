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

(cffi:defcfun tmplan-op-motion-plan-path-size amino-ffi:size-t
  (op :pointer))

(cffi:defcfun tmplan-op-motion-plan-config-count amino-ffi:size-t
  (op :pointer))

(cffi:defcfun tmplan-op-motion-plan-path :pointer
  (op :pointer))

(cffi:defcfun tmplan-op-reparent-get-frame :string
  (op :pointer))

(cffi:defcfun tmplan-op-reparent-get-new-parent :string
  (op :pointer))

;;; Wrappers ;;;

;;; Special variables for forieng tmplan translation
(defvar *plan-ops*)
(defvar *plan-config-names*)
(defvar *plan-scene-graph*)
(defvar *plan-config-map*)

(defgeneric translate-op (type pointer scene-graph config))

(defmethod translate-op ((type (eql :action)) pointer scene-graph config)
  (declare (ignore type)
           (type scene-graph scene-graph))
  (tm-op-action (tmplan-op-action-get pointer)
                scene-graph config))

(cffi:defcallback fetch-var :void
    ((context :pointer) (name :pointer))
  (declare (ignore context))
  (push (cffi:foreign-string-to-lisp name)
        *plan-config-names*))

(defmethod translate-op ((type (eql :motion-plan)) pointer scene-graph config)
  (declare (ignore type))
  (declare (type scene-graph scene-graph))
  (let* ((*plan-config-names* nil)
         (m-sg (robray::mutable-scene-graph scene-graph))
         (foreign-path-size (tmplan-op-motion-plan-path-size pointer))
         (foreign-config-count (tmplan-op-motion-plan-config-count pointer))
         (foreign-path (tmplan-op-motion-plan-path pointer))
         (local-config-count (robray::mutable-scene-graph-config-count m-sg))
         (point-count (/ foreign-path-size foreign-config-count))
         (path (make-vec (* local-config-count point-count))))
    ;; Extract config names
    (tmplan-op-motion-plan-map-var pointer
                                   (cffi:callback fetch-var)
                                   (cffi:null-pointer))
    (assert (= foreign-config-count (length *plan-config-names*)))
    ;; construct path
    (let* ((config-names (reverse *plan-config-names*))
           (config-indices (loop for name in config-names
                              collect (robray::mutable-scene-graph-config-index m-sg name))))
      (dotimes (j point-count)
        ;; TODO: Initialize configs from start
        ;; Fill from foreign
        (loop
           for i-n in config-indices
           for i-f from 0
           do (setf (aref path (+ (* j local-config-count) i-n))
                   (cffi:mem-aref foreign-path :double (+ (* j foreign-config-count) i-f)))))
      (tm-op-motion (robray::make-motion-plan :scene-graph scene-graph
                                              :mutable-scene-graph m-sg
                                              :config-names config-names
                                              :path path)))))

(defmethod translate-op ((type (eql :reparent)) pointer scene-graph config)
  (declare (ignore type)
           (type scene-graph scene-graph))
  (let ((frame (tmplan-op-reparent-get-frame pointer))
        (new-parent (tmplan-op-reparent-get-new-parent pointer)))
    (tm-op-reparent scene-graph new-parent frame
                    :configuration-map config)))


(cffi:defcallback translate-plan-op :void
    ((context :pointer) (op :pointer))
  ;; ignore the context argument and use special variables intead
  (declare (ignore context))
  (check-type *plan-scene-graph* scene-graph)
  (let* ((type (tmplan-op-type op))
         (op (translate-op type op *plan-scene-graph* *plan-config-map*)))
    (push op *plan-ops*)
    (setq *plan-scene-graph* (tm-op-final-scene-graph op)
          *plan-config-map* (tm-op-final-config op))))



(defun translate-tmplan (scene-graph config-map pointer)
  (declare (type scene-graph scene-graph))
  (let ((*plan-ops* nil))
    (setq *plan-config-map* config-map
          *plan-scene-graph* scene-graph)
    (tmplan-map-ops pointer
                    (cffi:callback translate-plan-op)
                    (cffi:null-pointer))
    (reverse *plan-ops*)))

(defun parse-tmplan (scene-graph config-map pathname)
  ;; Parse pathname using the thread-local memory region
  (let ((ptr (tmplan-parse-filename (rope-string (rope pathname))
                                    (cffi:null-pointer))))
    (let ((ops (if (cffi:null-pointer-p ptr)
                   (error "Could not parse plan file `~A'." pathname)
                   (unwind-protect
                        (translate-tmplan scene-graph config-map ptr)
                     (amino::aa-mem-region-local-pop ptr)))))
      (tm-plan-list ops))))

(defun display-tm-plan-file (scene-files start-config plan-file)
  (robray::win-display-motion-plan-sequence
   (tm-plan-motion-plans (parse-tmplan (robray::load-scene-files scene-files)
                                       (or start-config
                                           (robray::make-configuration-map))
                                       plan-file))))
