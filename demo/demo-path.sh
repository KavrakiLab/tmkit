# Set paths for demo run scripts

# Maybe set ROS_PACKAGE_PATH
if [ -z "$ROS_PACKAGE_PATH" ]; then
   export ROS_PACKAGE_PATH=/opt/ros/indigo/share
fi

export PATH="..:$PATH"
export LD_LIBRARY_PATH="../.libs:$LD_LIBRARY_PATH"
