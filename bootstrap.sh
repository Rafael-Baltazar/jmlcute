#!/bin/bash
wget --no-check-certificate https://github.com/aglover/ubuntu-equip/raw/master/equip_base.sh && bash equip_base.sh
wget --no-check-certificate https://github.com/aglover/ubuntu-equip/raw/master/equip_java7_64.sh && bash equip_java7_64.sh
NEWPATH=.:$PATH:/usr/lib/jvm/jdk1.7.0_65/bin
export PATH=$NEWPATH
echo "export PATH='$NEWPATH'" >> .bashrc
echo "cd /vagrant/" >> .bashrc
sudo apt-get update -y
sudo apt-get install -y dos2unix unzip tar vim
cd /vagrant/
chmod +x debugJMLCute
echo "Setup Complete"
echo "Try running ./debugJMLCute"

