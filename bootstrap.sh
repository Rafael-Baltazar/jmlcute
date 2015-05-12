#!/bin/bash
NEWPATH=.:$PATH:/usr/lib/jvm/jdk1.7.0_65/bin
export PATH=$NEWPATH
echo "export PATH='$NEWPATH'" >> .bashrc
sudo apt-get update -y
sudo apt-get install -y dos2unix unzip tar vim
cd /vagrant/
chmod +x jcutec
chmod +x jcute
chmod +x debugJMLCute
echo "Setup Complete"
echo "Try running ./debugJMLCute"

