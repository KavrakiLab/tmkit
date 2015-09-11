(in-package :tmsmt)

(defun act-plan-ws (context q-all-start link tf)
  (let ((container (plan-context-moveit-container context)))
    (container-set-start container q-all-start)
    (container-goal-clear container)
    (container-set-ws-goal container link tf)
    (container-scene-send container)
    (container-plan container)))


(defun act-pick-tf (context q-all-start link object-name relative-tf)
  (let* ((object-tf (robray::scene-graph-tf-absolute (plan-context-object-graph context)
                                                     object-name))
         (tf-grasp (g* object-tf relative-tf)))
    (act-plan-ws context q-all-start link tf-grasp)))

(defun act-place-tf (context q-all-start link destination-name relative-tf object-name )
  (let* ((g-tf-dst (robray::scene-graph-tf-absolute (plan-context-object-graph context)
                                                    destination-name))
         (g-tf-obj (g* g-tf-dst relative-tf))
         (e-tf-obj (robray::scene-frame-fixed-tf (robray::scene-graph-lookup (plan-context-object-graph context)
                                                                             object-name)))
         (g-tf-e (g* g-tf-obj (tf-inverse e-tf-obj))))
    (act-plan-ws context q-all-start link g-tf-e)))


;; TODO: don't change state if planning doesn't work
(defun act-transfer-tf (context group q-all-start
                              frame link object-name pick-rel-tf destination-name dst-rel-tf)
  (let ((plan-pick (act-pick-tf context q-all-start link object-name pick-rel-tf ))
        (object-graph-0 (plan-context-object-graph context)))
    (if (null plan-pick)
        (values nil object-graph-0 :pick object-name)
        (let* ((container (plan-context-moveit-container context))
               (q-group-pick (container-plan-endpoint plan-pick))
               (q-all-pick (container-merge-group container group q-group-pick q-all-start)))
          (context-attach-object context group q-group-pick frame link object-name)
          (let ((plan-place (act-place-tf context q-all-pick link
                                          destination-name
                                          dst-rel-tf
                                          object-name)))
            (context-dettach-object context group
                                    (container-plan-endpoint (or plan-place plan-pick))
                                    object-name
                                    destination-name)
            (if plan-place
                ;; TODO: parent on the destination thing
                (values (list plan-pick `(:pick ,object-name)
                              plan-place `(:place ,object-name))
                        (plan-context-object-graph context)
                        nil
                        object-name)
                (values nil object-graph-0 :place object-name)))))))
