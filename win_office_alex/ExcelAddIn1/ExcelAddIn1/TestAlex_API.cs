using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace ExcelAddIn1
{   
    //TODO get nunit testing assemblies
    //[TestFixture]
    class TestAlex_API
    {
        //[Test]
        public static void main(String[] args)
        {
            Alex_API.createWorksheet("Test.xls","sally");

        }

    }
}
