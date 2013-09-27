using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Windows.Forms;
using System.IO;

namespace ExcelAddIn1
{
    public partial class SettingsDialog : Form
    {
        public SettingsDialog()
        {
            InitializeComponent();
        }

        //select JAR file
        private void button1_Click(object sender, EventArgs e)
        {
            openFileDialog1 = new OpenFileDialog();
            MessageBox.Show(Properties.Settings.Default.Jar);
            if (File.Exists(Properties.Settings.Default.Jar))
            {
                openFileDialog1.InitialDirectory = Path.GetDirectoryName(Properties.Settings.Default.Jar);
            }
            else
            {
                openFileDialog1.InitialDirectory = "c:\\";
            }
            openFileDialog1.Filter = "jar files (*.jar)|*.jar";
            openFileDialog1.Multiselect = false;

            if (openFileDialog1.ShowDialog() == DialogResult.OK)
            {
                Properties.Settings.Default.Jar = openFileDialog1.FileName;
                Properties.Settings.Default.Save();
            }
            label1.Text = Properties.Settings.Default.Jar;
        }

        //select JAVA exe
        private void button2_Click(object sender, EventArgs e)
        {
            openFileDialog1 = new OpenFileDialog();
            MessageBox.Show(Properties.Settings.Default.Java);
            if (File.Exists(Properties.Settings.Default.Java))
            {
                openFileDialog1.InitialDirectory = Path.GetDirectoryName(Properties.Settings.Default.Java);
            }
            else
            {
                openFileDialog1.InitialDirectory = "c:\\";
            }
            openFileDialog1.Filter = "Java Executables (*.exe)|*.exe";
            openFileDialog1.Multiselect = false;

            if (openFileDialog1.ShowDialog() == DialogResult.OK)
            {
                Properties.Settings.Default.Java = openFileDialog1.FileName;
                Properties.Settings.Default.Save();
            }
            label2.Text = Properties.Settings.Default.Java;
        }

        private void SettingsDialog_Shown(object sender, EventArgs e)
        {
            label1.Text = Properties.Settings.Default.Jar;
            label2.Text = Properties.Settings.Default.Java;
        }
    }
}
