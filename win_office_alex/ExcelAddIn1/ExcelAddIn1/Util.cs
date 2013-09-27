using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Reflection;

using sally;

namespace ExcelAddIn1
{
    class Util
    {

        /// <summary>
        /// This method safely gets an object from the map and automatically casts it to a string. 
        /// This only works if the object is actually a string. 
        /// </summary>
        /// <param name="map">The map to get the object from</param>
        /// <param name="key">The key for which you want to get the value</param>
        /// <returns>The object cast to a string.</returns>
        // TODO Use generic code
        public static string tryGetString(Dictionary<String, Object> map, string key)
        {
            string result = "";
            try
            {
                result = (string)map[key];
            }
            catch (Exception ex) { Console.WriteLine(ex); }
            return result;
        }


        /// <summary>
        /// Restore a cometd message to a GoogleMessage
        /// </summary>
        /// <param name="message">The Cometd message.</param>
        /// <returns>Google.ProtocolBuffers message.</returns>
        public static Google.ProtocolBuffers.IMessage restoreMessage(Cometd.Bayeux.IMessage message)
        {
            Console.WriteLine(message);
            Dictionary<string, object> input = (Dictionary<string, object>)message;
            string type = tryGetString(input, "type");
            string s = tryGetString(input, "s");
            if (type == "" || s == "")
            {
                object myData = null;
                try
                {
                    myData = input["data"];
                }
                catch (Exception ex)
                { }
                Dictionary<string, object> newInput = (Dictionary<string, object>)myData;
                type = tryGetString(newInput, "type");
                s = tryGetString(newInput, "s");
                if (type == "" || s == "")
                    return null;
            }

            return Util.stringToProto(type, s);
        }



        /// <summary>
        /// Prepares the Protobuf message for sending via Cometd.
        /// </summary>
        /// <param name="message">Google ProtocolBuffers message</param>
        /// <returns>A dictionary with two elements.</returns>
        public static Dictionary<string, Object> prepareMessage(Google.ProtocolBuffers.IMessage message)
        {
            Dictionary<string, Object> output = new Dictionary<string, Object>();
            if (message != null)
            {
                output.Add("type", message.GetType().ToString());
                output.Add("s", Convert.ToBase64String(message.ToByteArray()));
            }
            return output;
        }

        /*
         * Gets the google protomessage from a type and a string that represents the encoded message
         */
        /// <summary>
        /// Given a type of message and the message as a string it restores it to a Google.ProtocolBuffers message.
        /// </summary>
        /// <param name="type">Type of Message</param>
        /// <param name="message">The Google message encoded as a string.</param>
        /// <returns>Google.ProtocolBuffers message.</returns>
        public static Google.ProtocolBuffers.IMessage stringToProto(String type, String message)
        {

            try
            {

                Type t = Type.GetType(type);
                MethodInfo o = t.GetMethod("ParseFrom", new[] { typeof(byte[]) });
                string restMessage = message;
                byte[] binaryData = Convert.FromBase64String(restMessage);
                object[] args = new object[1] { binaryData };
                object result = o.Invoke(null, args);

                if (result == null)
                    return null;

                return (Google.ProtocolBuffers.IMessage)result;

            }
            catch (Exception ex) { Console.WriteLine(ex); }

            return null;
        }



        /// <summary>
        /// Converts an address represented by letters to an integer. A is equivalent to 0.
        /// Excel counts from 1 but 0 is the standard for most applications.
        /// </summary>
        /// <param name="address">The string representing the address</param>
        /// <returns>Integer representing the index of the column. Numbering starts from A=0.</returns>
        public static int parseToInt(string address)
        {
            int sum = 0;

            for (int i = 0; i < address.Length - 1; i++)
                sum = sum * 26 + (address[i] - 'A' + 1);
            sum = sum * 26 + address[address.Length - 1] - 'A';
            return sum;
        }


        /// <summary>
        /// Converts a string representing the range to column-row ranges. Numbering starting from 0.
        /// </summary>
        /// <param name="address">A1 reference style e.g. A1:A5 </param>
        /// <param name="startCol">Int representing the starting column</param>
        /// <param name="startRow">Int representing the starting row</param>
        /// <param name="endCol">Int representing the end column</param>
        /// <param name="endRow">Int representing the end row </param>
        public static void convertRangeAddress(string address, out int startCol, out int startRow, out int endCol, out int endRow)
        {
            char[] delimiterChars = { '$', ';' };
            string[] words = address.Split(delimiterChars);

            startCol = parseToInt(words[1]);
            startRow = Convert.ToInt32(words[2]) - 1;
            if (words.Length > 3)
            {
                endCol = parseToInt(words[4]);
                endRow = Convert.ToInt32(words[5]) - 1;
            }
            else
            {
                endCol = startCol;
                endRow = startRow;
            }
        }

        /// <summary>
        /// Converst a column number into a string representing it.
        /// </summary>
        /// <param name="column">Index of the column</param>
        /// <returns>String representing the index of the column in the spreadsheet</returns>
        public static string parseToAddress(int column)
        {
            string result = "";
            result = (char)(column % 26 + 'A') + result;
            column /= 26;
            while (column != 0)
            {
                if (column % 26 == 0)
                {
                    result = 'Z' + result;
                    column--;
                }
                else
                    result = (char)(column % 26 + 'A' - 1) + result;
                column /= 26;
            }

            return result;
        }

        /// <summary>
        /// Translate a range consisting of the start and end coordinates of the cells in integers to a Excel specific range. 
        /// </summary>
        /// <param name="startRow">The index of the start row</param>
        /// <param name="endRow">The index of the end row</param>
        /// <param name="startCol">The index of the start col</param>
        /// <param name="endCol">The index of the end column</param>
        /// <returns>String representing an Excel range, A1 reference style</returns>
        public static string rangeToExcelAddress(int startRow, int endRow, int startCol, int endCol)
        {
            return "" + parseToAddress(startCol) + (startRow + 1) + ":" + parseToAddress(endCol) + (endRow + 1);

        }


        /// <summary>
        /// Returns string + int concatenation for a given address 
        /// </summary>
        /// <param name="addressPrefix">string e.g. "A"</param>
        /// <param name="addressSuffix">int e.g. "1"</param>
        /// <returns>string address e.g. "A1"</returns>
        public static string str_int_ToExcelAddress(string addressPrefix, int addressSuffix)
        {
            return addressPrefix + addressSuffix.ToString();
        }

        /// <summary>
        /// Returns string1+int1+":"+string2+int2 concatenation for a given address 
        /// </summary>
        /// <param name="addressPrefix"></param>
        /// <param name="addressSuffixBegin"></param>
        /// <param name="addressSuffixEnd"></param>
        /// <returns>string address e.g. "A" + 1 + 2 = "A1:A2"</returns>
        public static string str_int_ToExcelAddress(string addressPrefix, int addressSuffixBegin, int addressSuffixEnd){
            return str_int_ToExcelAddress(addressPrefix, addressSuffixBegin) + ":" + str_int_ToExcelAddress(addressPrefix, addressSuffixEnd);
        }

        /// <summary>
        /// Returns string1+int1+":"+string2+int2 concatenation for a given address 
        /// </summary>
        /// <param name="addressPrefix1"></param>
        /// <param name="addressSuffix1"></param>
        /// <param name="addressPrefix2"></param>
        /// <param name="addressSuffix2"></param>
        /// <returns>string address e.g. "A" + 1 + "B" + 2 = "A1:B2"</returns>
        public static string str_int_ToExcelAddress(string addressPrefix1, int addressSuffix1, string addressPrefix2, int addressSuffix2)
        {
            return str_int_ToExcelAddress(addressPrefix1, addressSuffix1) + ":" + str_int_ToExcelAddress(addressPrefix2, addressSuffix2);
        }


        public static List<string> columnToExcelAddressList(string addressPrefix, int addressSuffixBegin, int addressSuffixEnd ) 
        {
            List<string> addresses = new List<string>();
            
            //swap
            if (addressSuffixBegin > addressSuffixEnd) 
            {
                int temp = addressSuffixBegin;
                addressSuffixBegin = addressSuffixEnd;
                addressSuffixEnd = temp;
            }

            for (int i = addressSuffixBegin; i <= addressSuffixEnd; i++) 
            {
                addresses.Add(addressPrefix+i.ToString());
            }


                return addresses;
        }

    }
}
