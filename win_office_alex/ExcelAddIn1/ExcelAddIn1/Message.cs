using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace ExcelAddIn1
{
    class Message
    {
        public int reqid { get; set; }
        public String action { get; set; }
        public List<Parameter> param = new List<Parameter>();

        public Message() : this("") { }

        public Message(String action) : this(action, new Dictionary<string, string>()) { }

        public Message(String action, Dictionary<string, string> props)
        {
            this.reqid = new Random().Next();
            this.action = action;            
            foreach (KeyValuePair<string, string> entry in props)
            {
                Parameter p = new Parameter(entry.Key, entry.Value);
                param.Add(p);
            }
        }
    }

    class Parameter
    {
        public String pName { get; set; }
        public String pValue { get; set; }
        public Parameter(String pName, String pValue)
        {
            this.pName = pName;
            this.pValue = pValue;
        }
        public Parameter()
        {
            this.pName = "";
            this.pValue = "";
        }
    }
}
