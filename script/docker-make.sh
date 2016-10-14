#!/bin/sh -e

if [ -z "$JOBS" ]; then
    JOBS=8
fi

for DOCKERFILE in $@; do
    NAME="tmkit-${DOCKERFILE}-install"
    docker rm "$NAME" || true
    docker run --name="$NAME" "tmkit:$DOCKERFILE-dep" /bin/sh -c "cd /root/tmkit && autoreconf -i && ./configure --enable-demo-baxter && make -k -j $JOBS V=1 distcheck && make install" && \
        docker commit "$NAME" "tmkit:${DOCKERFILE}-install"
done
