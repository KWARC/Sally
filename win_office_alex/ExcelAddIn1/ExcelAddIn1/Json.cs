using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Web.Script.Serialization;

namespace ExcelAddIn1
{
    class Json
    {
        private static JavaScriptSerializer jss = new JavaScriptSerializer();
            
        public static Message deserialize(String str)
        {
            return jss.Deserialize<Message>(str);
        }

        public static String serialize(Message m)
        {
            return jss.Serialize(m);
        }
    }
}
