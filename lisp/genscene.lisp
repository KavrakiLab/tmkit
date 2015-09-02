(in-package :tmsmt)


(defun genscene-repeat-table (parent base-name shape count x y
                              &key
                                (rotation (quaternion nil))
                                (z .001)
                                (resolution .1d0)
                                (options robray::*draw-options*)
                                )
  (let* ((n-x (round (/ x resolution)))
         (n-y (round (/ y resolution)))
         (k-x (floor (/ n-x 2)))
         (k-y (floor (/ n-y 2)))
         (mark (make-array (list n-x n-y)
                           :initial-element nil))
         (g (scene-graph)))
    (assert (< count (* n-x n-y)))
    (dotimes (k  count)
      (loop
         for i = (random n-x)
         for j = (random n-y)
         while (aref mark i j)
         finally
           (let ((obj-x (* resolution (- i k-x)))
                 (obj-y (* resolution (- j k-y))))
             (assert (= (- i k-x) (round obj-x resolution)))
             (assert (= (- j k-y) (round obj-y resolution)))
             (assert (null (aref mark i j)))
             (setf (aref mark i j) t)
             (setq g (scene-graph g (scene-frame-fixed parent (format nil "~A-~D" base-name k)
                                                       :geometry (robray::scene-geometry shape
                                                                                         options)
                                                       :tf (tf* rotation
                                                                (vec3* (* resolution (- i (floor (/ n-x 2))))
                                                                       (* resolution (- j (floor (/ n-y 2))))
                                                                       z))))))))

    g))
