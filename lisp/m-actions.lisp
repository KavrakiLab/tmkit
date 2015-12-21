(in-package :tmsmt)

(defun act-plan-ws (sub-scene-graph start tf)
  ;(break)
  (robray::win-set-scene-graph (sub-scene-graph-scene-graph sub-scene-graph))
  (robray::win-set-config start)
  ;(print (list 'ws-plan start tf))
  (motion-plan sub-scene-graph start :workspace-goal tf :timeout 5d0))

(defun act-pick-tf (sg frame start object-name o-tf-e)
  ;(print (list 'pick frame object-name (tf-array o-tf-e)))
  (let* ((ssg (scene-graph-chain sg nil frame))
         (g-tf-o (scene-graph-tf-absolute sg object-name :configuration-map start))
         (g-tf-e (g* g-tf-o o-tf-e)))
    (let ((mp (act-plan-ws ssg start g-tf-e)))
      ;(print mp)
      (if (robray::motion-plan-valid-p mp)
          (values mp
                  (let* (;(end (motion-plan-endpoint-map mp))
                         ;(g-tf-ae (scene-graph-tf-absolute sg frame :configuration-map end))
                         ;(o-tf-ae (g* (tf-inverse g-tf-o) g-tf-ae))
                         )
                    ;(print (tf-array g-tf-e))
                    ;(print (tf-array g-tf-ae))
                    ;(print (tf-inverse relative-tf))
                    (scene-graph-reparent sg frame object-name
                                          ;:tf (g* (tf-inverse act-g-tf-e) g-tf-e)
                                          ;:tf o-tf-e
                                          :tf (tf-inverse o-tf-e)
                                          )
                    ;sg
                    ))
          (values nil sg)))))

(defun act-place-tf (sg frame start destination-name relative-tf object-name )
  ;(print 'place)
  (let* ((ssg (scene-graph-chain sg nil frame))
         (g-tf-dst (scene-graph-tf-absolute sg destination-name :configuration-map start))
         (g-tf-obj (g* g-tf-dst relative-tf))
         (e-tf-obj (robray::scene-frame-fixed-tf (robray::scene-graph-lookup sg object-name)))
         (g-tf-e (g* g-tf-obj (tf-inverse e-tf-obj))))
    (let ((mp (act-plan-ws ssg start g-tf-e)))
      ;(print mp)
      (if (robray::motion-plan-valid-p mp)
          (values mp
                  (scene-graph-reparent sg destination-name object-name :tf relative-tf))
          (values nil sg)))))

(defun act-transfer-tf (sg-0 frame start object-name pick-rel-tf destination-name dst-rel-tf)
  ;(print 'transfer)
  (multiple-value-bind (mp-pick sg)
      (act-pick-tf sg-0 frame start object-name pick-rel-tf )
    (if (null mp-pick)
        (values nil sg-0 :pick object-name)
        (multiple-value-bind (mp-place sg)
            (act-place-tf sg frame (motion-plan-endpoint-map mp-pick)
                          destination-name dst-rel-tf object-name)
          (if (null mp-place)
              (values nil sg-0 :place object-name)
              (values (list mp-pick `(:pick ,object-name)
                            mp-place `(:place ,object-name))
                      sg nil object-name))))))
