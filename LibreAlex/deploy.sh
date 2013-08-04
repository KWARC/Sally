export PATH=$PATH:/opt/libreoffice3.6/program
unopkg remove LibreAlex.uno.pkg
unopkg add LibreAlex.uno.pkg
scalc &
rm /tmp/libre.log
touch /tmp/libre.log
tail -f /tmp/libre.log
