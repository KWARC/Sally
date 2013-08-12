<h1>Sally Configuration page</h1>

<#list configs as config>
	<a href="${config.url}">${config.description}</a> <br>
</#list>