/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class AManyDeclLst extends PDeclLst
{
    private POneDecl _oneDecl_;
    private TSeparator _separator_;
    private PDeclLst _declLst_;

    public AManyDeclLst()
    {
        // Constructor
    }

    public AManyDeclLst(
        @SuppressWarnings("hiding") POneDecl _oneDecl_,
        @SuppressWarnings("hiding") TSeparator _separator_,
        @SuppressWarnings("hiding") PDeclLst _declLst_)
    {
        // Constructor
        setOneDecl(_oneDecl_);

        setSeparator(_separator_);

        setDeclLst(_declLst_);

    }

    @Override
    public Object clone()
    {
        return new AManyDeclLst(
            cloneNode(this._oneDecl_),
            cloneNode(this._separator_),
            cloneNode(this._declLst_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseAManyDeclLst(this);
    }

    public POneDecl getOneDecl()
    {
        return this._oneDecl_;
    }

    public void setOneDecl(POneDecl node)
    {
        if(this._oneDecl_ != null)
        {
            this._oneDecl_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._oneDecl_ = node;
    }

    public TSeparator getSeparator()
    {
        return this._separator_;
    }

    public void setSeparator(TSeparator node)
    {
        if(this._separator_ != null)
        {
            this._separator_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._separator_ = node;
    }

    public PDeclLst getDeclLst()
    {
        return this._declLst_;
    }

    public void setDeclLst(PDeclLst node)
    {
        if(this._declLst_ != null)
        {
            this._declLst_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._declLst_ = node;
    }

    @Override
    public String toString()
    {
        return ""
            + toString(this._oneDecl_)
            + toString(this._separator_)
            + toString(this._declLst_);
    }

    @Override
    void removeChild(@SuppressWarnings("unused") Node child)
    {
        // Remove child
        if(this._oneDecl_ == child)
        {
            this._oneDecl_ = null;
            return;
        }

        if(this._separator_ == child)
        {
            this._separator_ = null;
            return;
        }

        if(this._declLst_ == child)
        {
            this._declLst_ = null;
            return;
        }

        throw new RuntimeException("Not a child.");
    }

    @Override
    void replaceChild(@SuppressWarnings("unused") Node oldChild, @SuppressWarnings("unused") Node newChild)
    {
        // Replace child
        if(this._oneDecl_ == oldChild)
        {
            setOneDecl((POneDecl) newChild);
            return;
        }

        if(this._separator_ == oldChild)
        {
            setSeparator((TSeparator) newChild);
            return;
        }

        if(this._declLst_ == oldChild)
        {
            setDeclLst((PDeclLst) newChild);
            return;
        }

        throw new RuntimeException("Not a child.");
    }
}
