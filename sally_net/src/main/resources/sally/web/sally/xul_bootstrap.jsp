<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd">
<html>
<head>

<meta http-equiv="Content-Type" content="text/html;charset=utf-8" />

<script type="text/javascript">
	var config = {
		contextPath : '/sally'
	};
</script>
<script type="text/javascript" src="jquery/jquery-1.7.2.js"></script>
<script type="text/javascript" src="jquery/json2.js"></script>
<script type="text/javascript" src="org/cometd.js"></script>
<script type="text/javascript" src="jquery/jquery.cometd.js"></script>
<script type="text/javascript" src="comm/dataview.js"></script>
<script type="text/javascript" src="comm/protobuf.js"></script>
<script type="text/javascript" src="comm/common.js"></script>
<script type="text/javascript" src="comm/util.js"></script>
<script type="text/javascript" src="xul_main.js"></script>


</head>
<body>
	<button type="button"
		onclick='openNewWindow({"x":200,"y":100,"url":"file:///D:/Projects/sissi/trunk/xultheo3/chrome/content/test.html"})'>Open
		Real Window </button>
	<button type="button"
		onclick='openNewWindow({"x":200,"y":100,"url":"http://localhost:8080/sally/web/frames"});'>Open
		Sally Frame Window </button>
	<div id="body"></div>


</body>
</html>
