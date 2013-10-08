<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="2.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns:m="http://www.w3.org/1998/Math/MathML">
<xsl:output method="text" encoding="UTF-8"/>

<xsl:template match="m:apply">
  <xsl:text>(</xsl:text> <xsl:apply-templates/>
  <xsl:text>)</xsl:text> 
</xsl:template>

<xsl:template match="m:csymbol">
  <xsl:value-of select="@cd"/>
  <xsl:text>~</xsl:text> 
  <xsl:value-of select="."/>
  <xsl:text> </xsl:text> 
</xsl:template>

<xsl:template match="m:bvar/m:ci">
  <xsl:text> </xsl:text> 
</xsl:template>

<xsl:template match="m:ci">
  <xsl:value-of select="."/>
  <xsl:text> </xsl:text> 
</xsl:template>

<xsl:template match="m:cn">
  <xsl:value-of select="."/>
  <xsl:text> </xsl:text> 
</xsl:template>

<xsl:template match="m:plus">
  <xsl:text>+ </xsl:text> 
</xsl:template>

<xsl:template match="m:minus">
  <xsl:text>- </xsl:text> 
</xsl:template>

<xsl:template match="m:eq">
  <xsl:text>= </xsl:text> 
</xsl:template>

<xsl:template match="m:forall">
  <xsl:text>forall </xsl:text> 
</xsl:template>

<xsl:template match="m:condition">
  <xsl:text>(</xsl:text> 
  <xsl:value-of select="."/>
  <xsl:text>)</xsl:text> 
</xsl:template>

<xsl:template match="m:condition/m:apply/m:and">
  <xsl:text>(</xsl:text> 
  <xsl:value-of select="."/>
  <xsl:text>)</xsl:text> 
</xsl:template>

</xsl:stylesheet>
