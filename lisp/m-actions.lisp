(in-package :tmsmt)

(defun act-plan-ws (sub-scene-graph start tf)
  (motion-plan sub-scene-graph start :workspace-goal tf))

(defun act-pick-tf (sg frame start object-name relative-tf)
  (let* ((ssg (scene-graph-chain sg nil frame))
         (object-tf (scene-graph-tf-absolute sg object-name :configuration-map start))
         (tf-grasp (g* object-tf relative-tf)))
    (let ((mp (act-plan-ws ssg start tf-grasp)))
      (print mp)
      (if mp
          (values mp
                  (scene-graph-reparent sg frame object-name :tf (tf-inverse relative-tf))
          (values nil sg))))))

(defun act-place-tf (sg frame start destination-name relative-tf object-name )
  (let* ((ssg (scene-graph-chain sg nil frame))
         (g-tf-dst (scene-graph-tf-absolute sg destination-name))
         (g-tf-obj (g* g-tf-dst relative-tf))
         (e-tf-obj (robray::scene-frame-fixed-tf (robray::scene-graph-lookup sg object-name)))
         (g-tf-e (g* g-tf-obj (tf-inverse e-tf-obj))))
    (let ((mp (act-plan-ws ssg start g-tf-e)))
      (print mp)
      (if mp
          (values mp
                  (scene-graph-reparent sg frame object-name :tf relative-tf))
          (values nil sg)))))

(defun act-transfer-tf (sg-0 frame start object-name pick-rel-tf destination-name dst-rel-tf)
  (multiple-value-bind (mp-pick sg)
      (act-pick-tf sg-0 frame start object-name pick-rel-tf )
    (if (null mp-pick)
        (values nil sg-0 :pick object-name)
        (multiple-value-bind (mp-place sg)
            (act-place-tf sg frame start destination-name dst-rel-tf object-name)
          (if (null mp-place)
              (values nil sg-0 :place object-name)
              (values (list mp-pick `(:pick ,object-name)
                            mp-place `(:place ,object-name))
                      sg nil object-name))))))
